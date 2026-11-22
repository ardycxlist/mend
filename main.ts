// mend: a patch tool for the edits AI models write.
//
// Reads one patch (unified diff, SEARCH/REPLACE blocks, V4A, or JSON
// tool-call edits) and applies every edit it holds to the tree of text
// files in the working directory, or applies none of them when any edit
// fails. The whole contract lives in SPEC.md; this file implements it
// section by section. Node 22, standard library only.
//
// Usage: node main.ts [--format=NAME] [--check] [--strict] [PATCH]
// PATCH is a patch file, or "-" / absent for standard input.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const KNOWN_FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** Thrown to answer exit 2 with one line. */
class UsageFault {
  readonly text: string;
  constructor(text: string) {
    this.text = text;
  }
}

/** Thrown by one edit to report its failure code and path. */
class EditFault {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const isBlank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r stripped, no empty tail. */
function splitPatch(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function pathIsSafe(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((seg) => seg !== '' && seg !== '.' && seg !== '..');
}

const stripRight = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};

/** A file broken into lines plus its own line break and final-break flag. */
interface FileView {
  lines: string[];
  br: string;
  endsNl: boolean;
}

function viewFile(text: string): FileView {
  if (text === '') return { lines: [], br: '\n', endsNl: false };
  const firstNl = text.indexOf('\n');
  const br = firstNl > 0 && text[firstNl - 1] === '\r' ? '\r\n' : '\n';
  const pieces = text.split(br);
  const endsNl = text.endsWith(br);
  if (endsNl) pieces.pop();
  return { lines: pieces, br, endsNl };
}

function joinView(v: FileView): string {
  if (v.lines.length === 0) return '';
  return v.lines.join(v.br) + (v.endsNl ? v.br : '');
}

/** The tree as the edits leave it; untouched paths still read from disk. */
class Tree {
  private diskText = new Map<string, string | null>();
  private diskExists = new Map<string, boolean>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  private load(p: string): void {
    if (this.diskText.has(p)) return;
    let text: string | null = null;
    let exists = false;
    try {
      const st = statSync(p);
      exists = true;
      if (st.isFile()) text = readFileSync(p, 'utf8');
    } catch {
      exists = false;
    }
    this.diskText.set(p, text);
    this.diskExists.set(p, exists);
  }

  original(p: string): string | null {
    this.load(p);
    return this.diskText.get(p)!;
  }

  startedAs(p: string): boolean {
    this.load(p);
    return this.diskExists.get(p)!;
  }

  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }

  present(p: string): boolean {
    return this.now.has(p) ? this.now.get(p)! !== null : this.startedAs(p);
  }

  put(p: string, v: string | null): void {
    this.now.set(p, v);
  }
}

type EditFn = (tree: Tree) => void;

function linesEqualAt(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripRight(a) === stripRight(b);
  return stripBoth(a) === stripBoth(b);
}

/** Every 0-based position where old lines match the file lines at a tier. */
function occurrencesAt(lines: string[], old: string[], tier: number): number[] {
  const hits: number[] = [];
  if (old.length === 0 || old.length > lines.length) return hits;
  for (let i = 0; i + old.length <= lines.length; i += 1) {
    let ok = true;
    for (let k = 0; k < old.length; k += 1) {
      if (!linesEqualAt(lines[i + k]!, old[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) hits.push(i);
  }
  return hits;
}

/** The first tier (0, 1, 2) at which old occurs at least once, or null. */
function locate(lines: string[], old: string[], strict: boolean): { tier: number; at: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const at = occurrencesAt(lines, old, tier);
    if (at.length > 0) return { tier, at };
  }
  return null;
}

/** One line of a replacement: context lines point back at an old line. */
interface NewLine {
  text: string;
  ctx: number | null;
}

/**
 * Build the lines that replace a matched block. Context lines come back as
 * the file's own matched lines; at tier 2 the other lines are re-indented
 * from the old block's first-line indent to the file's.
 */
function replacementLines(fileLines: string[], at: number, old: string[], next: NewLine[], tier: number): string[] {
  const out: string[] = [];
  const fileLead = tier === 2 && old.length > 0 ? leadWs(fileLines[at]!) : '';
  const oldLead = tier === 2 && old.length > 0 ? leadWs(old[0]!) : '';
  for (const item of next) {
    if (item.ctx !== null) {
      out.push(fileLines[at + item.ctx]!);
      continue;
    }
    let s = item.text;
    if (tier === 2 && old.length > 0 && s !== '' && s.trim() !== '' && s.startsWith(oldLead)) {
      s = fileLead + s.slice(oldLead.length);
    }
    out.push(s);
  }
  return out;
}

/** Apply hunks of one unified section to a file's text (SPEC section 6). */
function applyHunks(content: string, hunks: Hunk[], path: string, strict: boolean): string {
  const view = viewFile(content);
  const lines = view.lines;
  let drift = 0;
  for (const hunk of hunks) {
    if (hunk.old.length === 0) {
      const oldLen = lines.length;
      const spot = Math.min(hunk.a + drift, oldLen);
      const fresh = hunk.next.map((n) => n.text);
      lines.splice(spot, 0, ...fresh);
      if (spot >= oldLen) view.endsNl = !hunk.noFinal;
      drift += fresh.length;
      continue;
    }
    const found = locate(lines, hunk.old, strict);
    if (found === null) throw new EditFault('no-match', path);
    const want = hunk.a - 1 + drift;
    let best = found.at[0]!;
    for (const pos of found.at) {
      if (Math.abs(pos - want) < Math.abs(best - want)) best = pos;
    }
    const atEnd = best + hunk.old.length === lines.length;
    const fresh = replacementLines(lines, best, hunk.old, hunk.next, found.tier);
    lines.splice(best, hunk.old.length, ...fresh);
    if (atEnd) view.endsNl = !hunk.noFinal;
    drift += hunk.next.length - hunk.old.length;
  }
  view.lines = lines;
  return joinView(view);
}

interface Hunk {
  a: number;
  old: string[];
  next: NewLine[];
  /** a \ line follows the hunk's last context or + line */
  noFinal: boolean;
  /** a \ line follows the hunk's last + line */
  noFinalPlus: boolean;
}

function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const head = lines[first]!.trimStart()[0];
  if (head === '[' || head === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (
    lines.some(
      (l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')),
    )
  ) {
    return 'unified';
  }
  return null;
}

/* ------------------------------------------------------------------ */
/* JSON edits (SPEC section 9)                                         */
/* ------------------------------------------------------------------ */

function jsonEdit(value: unknown): EditFn | null {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return null;
  const obj = value as Record<string, unknown>;
  if (typeof obj.path !== 'string') return null;
  const p = obj.path;
  if (obj.command === 'create') {
    if (typeof obj.file_text !== 'string') return null;
    const text = obj.file_text;
    return (tree) => {
      if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
      if (tree.present(p)) throw new EditFault('exists', p);
      tree.put(p, text);
    };
  }
  if (obj.command === 'str_replace') {
    if (typeof obj.old_str !== 'string' || obj.old_str === '') return null;
    if (obj.new_str !== undefined && typeof obj.new_str !== 'string') return null;
    const oldStr = obj.old_str;
    const newStr = (obj.new_str as string | undefined) ?? '';
    return (tree) => {
      if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new EditFault('missing', p);
      const firstNl = before.indexOf('\n');
      const crlf = firstNl > 0 && before[firstNl - 1] === '\r';
      const norm = (s: string): string => (crlf ? s.split('\r\n').join('\n') : s);
      const hay = norm(before);
      const needle = norm(oldStr);
      let count = 0;
      for (let k = hay.indexOf(needle); k >= 0; k = hay.indexOf(needle, k + 1)) count += 1;
      if (count === 0) throw new EditFault('no-match', p);
      if (count > 1) throw new EditFault('ambiguous', p);
      const at = hay.indexOf(needle);
      const out = hay.slice(0, at) + norm(newStr) + hay.slice(at + needle.length);
      tree.put(p, crlf ? out.split('\n').join('\r\n') : out);
    };
  }
  if (obj.command === 'insert') {
    if (typeof obj.insert_line !== 'number' || !Number.isInteger(obj.insert_line)) return null;
    if (typeof obj.new_str !== 'string') return null;
    const atLine = obj.insert_line;
    const extra = splitPatch(obj.new_str);
    return (tree) => {
      if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new EditFault('missing', p);
      const view = viewFile(before);
      if (atLine < 0 || atLine > view.lines.length) throw new EditFault('no-match', p);
      const lines = [...view.lines];
      lines.splice(atLine, 0, ...extra);
      tree.put(p, joinView({ lines, br: view.br, endsNl: view.endsNl }));
    };
  }
  return null;
}

function parseJson(text: string, lines: string[]): EditFn[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new UsageFault('error: parse 1');
  const edits: EditFn[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let parsed: unknown;
    try {
      parsed = JSON.parse(text);
    } catch {
      throw new UsageFault(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(parsed)) throw new UsageFault(`error: parse ${first + 1}`);
    for (const item of parsed) {
      const edit = jsonEdit(item);
      if (edit === null) throw new UsageFault(`error: parse ${first + 1}`);
      edits.push(edit);
    }
    return edits;
  }
  lines.forEach((line, idx) => {
    if (isBlank(line)) return;
    let edit: EditFn | null = null;
    try {
      edit = jsonEdit(JSON.parse(line));
    } catch {
      edit = null;
    }
    if (edit === null) throw new UsageFault(`error: parse ${idx + 1}`);
    edits.push(edit);
  });
  return edits;
}

/* ------------------------------------------------------------------ */
/* Unified diffs (SPEC section 6)                                      */
/* ------------------------------------------------------------------ */

function headerPath(line: string): string {
  let s = line.slice(4).split('\t')[0]!.trim();
  if (s.startsWith('a/') || s.startsWith('b/')) s = s.slice(2);
  return s;
}

function parseHunk(lines: string[], at: number): { hunk: Hunk; next: number } {
  const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(lines[at]!);
  if (m === null) throw new UsageFault(`error: parse ${at + 1}`);
  const a = Number(m[1]);
  const body: string[] = [];
  let j = at + 1;
  while (j < lines.length) {
    const bl = lines[j]!;
    if (bl.startsWith('diff --git ')) break;
    if (bl.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
      body.push(bl);
      j += 1;
      continue;
    }
    break;
  }
  while (body.length > 0 && body[body.length - 1] === '') body.pop();
  let lastCtxPlus = -1;
  let lastPlus = -1;
  body.forEach((bl, idx) => {
    if (bl === '' || bl.startsWith(' ') || bl.startsWith('+')) lastCtxPlus = idx;
    if (bl.startsWith('+')) lastPlus = idx;
  });
  const noFinal = lastCtxPlus >= 0 && (body[lastCtxPlus + 1] ?? '').startsWith('\\');
  const noFinalPlus = lastPlus >= 0 && (body[lastPlus + 1] ?? '').startsWith('\\');
  const old: string[] = [];
  const next: NewLine[] = [];
  for (const bl of body) {
    if (bl.startsWith('\\')) continue;
    if (bl.startsWith(' ')) {
      const t = bl.slice(1);
      old.push(t);
      next.push({ text: t, ctx: old.length - 1 });
    } else if (bl === '') {
      old.push('');
      next.push({ text: '', ctx: old.length - 1 });
    } else if (bl.startsWith('-')) {
      old.push(bl.slice(1));
    } else if (bl.startsWith('+')) {
      next.push({ text: bl.slice(1), ctx: null });
    }
  }
  return { hunk: { a, old, next, noFinal, noFinalPlus }, next: j };
}

interface SectionSeed {
  diffOld?: string;
  diffNew?: string;
}

/** Parse one section; returns the index where the section ended. */
function parseSection(lines: string[], start: number, seed: SectionSeed, strict: boolean, out: EditFn[]): number {
  let i = start;
  let pairOld: string | null = null;
  let pairNew: string | null = null;
  let renOld: string | null = null;
  let renNew: string | null = null;
  let creation = false;
  let deletion = false;
  const hunks: Hunk[] = [];
  let inHeader = true;
  while (i < lines.length) {
    const line = lines[i]!;
    if (inHeader) {
      if (line.startsWith('--- ')) {
        const after = lines[i + 1] ?? '';
        if (!after.startsWith('+++ ')) throw new UsageFault(`error: parse ${i + 2}`);
        if (pairOld !== null) break;
        pairOld = headerPath(line);
        pairNew = headerPath(after);
        i += 2;
        continue;
      }
      if (line.startsWith('rename from ')) {
        renOld = line.slice('rename from '.length).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('rename to ')) {
        renNew = line.slice('rename to '.length).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('new file mode')) {
        creation = true;
        i += 1;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        deletion = true;
        i += 1;
        continue;
      }
      if (line.startsWith('diff --git ')) break;
      if (line.startsWith('@@')) {
        inHeader = false;
        continue;
      }
      i += 1;
      continue;
    }
    if (line.startsWith('@@')) {
      const parsed = parseHunk(lines, i);
      hunks.push(parsed.hunk);
      i = parsed.next;
      continue;
    }
    break;
  }
  const oldPath = pairOld ?? renOld ?? seed.diffOld ?? null;
  const newPath = pairNew ?? renNew ?? seed.diffNew ?? null;
  if (oldPath === null && newPath === null) return i;
  const isCreate = oldPath === '/dev/null' || creation;
  const isDelete = newPath === '/dev/null' || deletion;
  if (isCreate) {
    const target = newPath ?? oldPath!;
    const added: string[] = [];
    let noFinal = false;
    for (const h of hunks) {
      for (const n of h.next) added.push(n.text);
    }
    for (let k = hunks.length - 1; k >= 0; k -= 1) {
      if (hunks[k]!.next.some((n) => n.ctx === null)) {
        noFinal = hunks[k]!.noFinalPlus;
        break;
      }
    }
    out.push((tree) => {
      if (!pathIsSafe(target)) throw new EditFault('unsafe', target);
      if (tree.present(target)) throw new EditFault('exists', target);
      tree.put(target, added.length === 0 ? '' : added.join('\n') + (noFinal ? '' : '\n'));
    });
  } else if (isDelete) {
    const target = oldPath!;
    out.push((tree) => {
      if (!pathIsSafe(target)) throw new EditFault('unsafe', target);
      if (!tree.present(target)) throw new EditFault('missing', target);
      tree.put(target, null);
    });
  } else if (oldPath !== newPath) {
    const from = oldPath!;
    const to = newPath!;
    out.push((tree) => {
      if (!pathIsSafe(from)) throw new EditFault('unsafe', from);
      if (!pathIsSafe(to)) throw new EditFault('unsafe', to);
      const before = tree.get(from);
      if (before === null) throw new EditFault('missing', from);
      if (tree.present(to)) throw new EditFault('exists', to);
      const after = applyHunks(before, hunks, from, strict);
      tree.put(from, null);
      tree.put(to, after);
      tree.moves.push([from, to]);
    });
  } else {
    const target = oldPath!;
    out.push((tree) => {
      if (!pathIsSafe(target)) throw new EditFault('unsafe', target);
      const before = tree.get(target);
      if (before === null) throw new EditFault('missing', target);
      tree.put(target, applyHunks(before, hunks, target, strict));
    });
  }
  return i;
}

function parseUnified(lines: string[], strict: boolean): EditFn[] {
  const edits: EditFn[] = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(line);
      if (m === null) throw new UsageFault(`error: parse ${i + 1}`);
      i = parseSection(lines, i + 1, { diffOld: m[1], diffNew: m[2] }, strict, edits);
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      i = parseSection(lines, i, {}, strict, edits);
    } else if (line.startsWith('@@')) {
      throw new UsageFault(`error: parse ${i + 1}`);
    } else {
      i += 1;
    }
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* SEARCH/REPLACE blocks (SPEC section 7)                              */
/* ------------------------------------------------------------------ */

function parseSearchReplace(lines: string[], strict: boolean): EditFn[] {
  const edits: EditFn[] = [];
  let i = 0;
  let prevEnd = 0;
  let prevPath: string | null = null;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchAt = i;
    let path: string | null = null;
    for (let j = searchAt - 1; j >= prevEnd; j -= 1) {
      const cand = lines[j]!;
      if (isBlank(cand)) continue;
      const trimmed = cand.trim();
      if (trimmed.startsWith('```')) continue;
      path = trimmed;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new UsageFault(`error: parse ${searchAt + 1}`);
      path = prevPath;
    }
    let sep = -1;
    for (let j = searchAt + 1; j < lines.length; j += 1) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        sep = j;
        break;
      }
      if (t === '<<<<<<< SEARCH' || t === '>>>>>>> REPLACE') throw new UsageFault(`error: parse ${searchAt + 1}`);
    }
    if (sep < 0) throw new UsageFault(`error: parse ${searchAt + 1}`);
    let end = -1;
    for (let j = sep + 1; j < lines.length; j += 1) {
      const t = lines[j]!.trimEnd();
      if (t === '>>>>>>> REPLACE') {
        end = j;
        break;
      }
      if (t === '<<<<<<< SEARCH') throw new UsageFault(`error: parse ${searchAt + 1}`);
    }
    if (end < 0) throw new UsageFault(`error: parse ${searchAt + 1}`);
    const oldLines = lines.slice(searchAt + 1, sep);
    const newLines = lines.slice(sep + 1, end).map((l) => ({ text: l, ctx: null as number | null }));
    const p = path;
    const oldCopy = [...oldLines];
    const newCopy = [...newLines];
    if (oldCopy.length === 0) {
      edits.push((tree) => {
        if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
        if (tree.present(p)) throw new EditFault('exists', p);
        tree.put(p, newCopy.length === 0 ? '' : newCopy.map((n) => n.text).join('\n') + '\n');
      });
    } else {
      edits.push((tree) => {
        if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
        const before = tree.get(p);
        if (before === null) throw new EditFault('missing', p);
        const view = viewFile(before);
        const found = locate(view.lines, oldCopy, strict);
        if (found === null) throw new EditFault('no-match', p);
        if (found.at.length > 1) throw new EditFault('ambiguous', p);
        const at = found.at[0]!;
        const fresh = replacementLines(view.lines, at, oldCopy, newCopy, found.tier);
        const out = [...view.lines];
        out.splice(at, oldCopy.length, ...fresh);
        tree.put(p, joinView({ lines: out, br: view.br, endsNl: view.endsNl }));
      });
    }
    prevPath = path;
    prevEnd = end + 1;
    i = end + 1;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* V4A patches (SPEC section 8)                                        */
/* ------------------------------------------------------------------ */

interface V4aChunk {
  anchor: string;
  eof: boolean;
  old: string[];
  next: NewLine[];
}

function sectionStartKind(line: string): 'add' | 'delete' | 'update' | null {
  if (line.startsWith('*** Add File: ')) return 'add';
  if (line.startsWith('*** Delete File: ')) return 'delete';
  if (line.startsWith('*** Update File: ')) return 'update';
  return null;
}

function sectionPath(line: string, marker: string): string {
  return line.slice(marker.length).trim();
}

/** Gather a section's lines (with 1-based numbers) up to the next section. */
function collectSection(
  lines: string[],
  start: number,
  end: number,
): { rows: Array<[string, number]>; next: number } {
  const rows: Array<[string, number]> = [];
  let i = start;
  while (i < end) {
    if (sectionStartKind(lines[i]!) !== null) break;
    rows.push([lines[i]!, i + 1]);
    i += 1;
  }
  while (rows.length > 0 && isBlank(rows[rows.length - 1]![0])) rows.pop();
  return { rows, next: i };
}

function parseV4a(lines: string[], strict: boolean): EditFn[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new UsageFault('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new UsageFault(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!isBlank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new UsageFault(`error: parse ${lines.length + 1}`);
  const edits: EditFn[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (isBlank(line)) {
      i += 1;
      continue;
    }
    const kind = sectionStartKind(line);
    if (kind === null) throw new UsageFault(`error: parse ${i + 1}`);
    if (kind === 'add') {
      const p = sectionPath(line, '*** Add File: ');
      const { rows, next } = collectSection(lines, i + 1, last);
      const fileLines: string[] = [];
      for (const [text, ln] of rows) {
        if (text.startsWith('+')) fileLines.push(text.slice(1));
        else if (text === '') fileLines.push('');
        else throw new UsageFault(`error: parse ${ln}`);
      }
      edits.push((tree) => {
        if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
        if (tree.present(p)) throw new EditFault('exists', p);
        tree.put(p, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
      i = next;
      continue;
    }
    if (kind === 'delete') {
      const p = sectionPath(line, '*** Delete File: ');
      const { rows, next } = collectSection(lines, i + 1, last);
      for (const [text, ln] of rows) {
        if (!isBlank(text)) throw new UsageFault(`error: parse ${ln}`);
      }
      edits.push((tree) => {
        if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
        if (!tree.present(p)) throw new EditFault('missing', p);
        tree.put(p, null);
      });
      i = next;
      continue;
    }
    const p = sectionPath(line, '*** Update File: ');
    const updateLine = i + 1;
    const { rows, next } = collectSection(lines, i + 1, last);
    let moveTo: string | null = null;
    let rest = rows;
    if (rows.length > 0 && rows[0]![0].startsWith('*** Move to: ')) {
      moveTo = sectionPath(rows[0]![0], '*** Move to: ');
      rest = rows.slice(1);
    }
    const chunks: V4aChunk[] = [];
    let current: V4aChunk | null = null;
    let afterEof = false;
    let seenChunk = false;
    for (const [text, ln] of rest) {
      if (text.startsWith('@@')) {
        if (current !== null) chunks.push(current);
        current = { anchor: text.slice(2).trim(), eof: false, old: [], next: [] };
        seenChunk = true;
        afterEof = false;
        continue;
      }
      if (text === '*** End of File') {
        if (current === null) throw new UsageFault(`error: parse ${ln}`);
        current.eof = true;
        chunks.push(current);
        current = null;
        afterEof = true;
        continue;
      }
      if (text.startsWith(' ') || text.startsWith('-') || text.startsWith('+') || text === '') {
        if (afterEof) throw new UsageFault(`error: parse ${ln}`);
        if (current === null) {
          if (seenChunk) throw new UsageFault(`error: parse ${ln}`);
          current = { anchor: '', eof: false, old: [], next: [] };
          seenChunk = true;
        }
        if (text.startsWith(' ')) {
          const t = text.slice(1);
          current.old.push(t);
          current.next.push({ text: t, ctx: current.old.length - 1 });
        } else if (text === '') {
          current.old.push('');
          current.next.push({ text: '', ctx: current.old.length - 1 });
        } else if (text.startsWith('-')) {
          current.old.push(text.slice(1));
        } else {
          current.next.push({ text: text.slice(1), ctx: null });
        }
        continue;
      }
      throw new UsageFault(`error: parse ${ln}`);
    }
    if (current !== null) chunks.push(current);
    if (chunks.length === 0 && moveTo === null) throw new UsageFault(`error: parse ${updateLine}`);
    const chunkList = chunks;
    const dest = moveTo;
    edits.push((tree) => {
      if (!pathIsSafe(p)) throw new EditFault('unsafe', p);
      if (dest !== null && !pathIsSafe(dest)) throw new EditFault('unsafe', dest);
      const before = tree.get(p);
      if (before === null) throw new EditFault('missing', p);
      if (dest !== null && tree.present(dest)) throw new EditFault('exists', dest);
      const view = viewFile(before);
      const linesNow = view.lines;
      let cursor = 0;
      for (const chunk of chunkList) {
        if (chunk.anchor !== '') {
          let foundAt = -1;
          const tiers = strict ? [0] : [0, 1, 2];
          for (const tier of tiers) {
            for (let j = cursor; j < linesNow.length; j += 1) {
              if (linesEqualAt(linesNow[j]!, chunk.anchor, tier)) {
                foundAt = j;
                break;
              }
            }
            if (foundAt >= 0) break;
          }
          if (foundAt < 0) throw new EditFault('no-match', p);
          cursor = foundAt + 1;
        }
        if (chunk.old.length === 0) {
          const spot = chunk.eof ? linesNow.length : cursor;
          linesNow.splice(spot, 0, ...chunk.next.map((n) => n.text));
          cursor = spot + chunk.next.length;
          continue;
        }
        let hit: { tier: number; at: number } | null = null;
        const tiers = strict ? [0] : [0, 1, 2];
        for (const tier of tiers) {
          const all = occurrencesAt(linesNow, chunk.old, tier).filter((pos) => pos >= cursor);
          const fitting = chunk.eof ? all.filter((pos) => pos + chunk.old.length === linesNow.length) : all;
          if (fitting.length > 0) {
            hit = { tier, at: fitting[0]! };
            break;
          }
        }
        if (hit === null) throw new EditFault('no-match', p);
        const fresh = replacementLines(linesNow, hit.at, chunk.old, chunk.next, hit.tier);
        linesNow.splice(hit.at, chunk.old.length, ...fresh);
        cursor = hit.at + fresh.length;
      }
      const after = joinView({ lines: linesNow, br: view.br, endsNl: view.endsNl });
      if (dest !== null) {
        tree.put(p, null);
        tree.put(dest, after);
        tree.moves.push([p, dest]);
      } else {
        tree.put(p, after);
      }
    });
    i = next;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* Running the CLI (SPEC sections 1, 2, 10)                            */
/* ------------------------------------------------------------------ */

function byteOrder(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

function runCli(argv: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const positional: string[] = [];
  let ended = false;
  for (const arg of argv) {
    if (!ended && arg === '--') {
      ended = true;
      continue;
    }
    if (!ended && arg.startsWith('-') && arg !== '-') {
      if (arg.startsWith('--format=')) {
        if (format !== null) return { code: 2, out: ['error: usage'] };
        const value = arg.slice('--format='.length);
        if (!KNOWN_FORMATS.includes(value)) return { code: 2, out: ['error: usage'] };
        format = value;
      } else if (arg === '--check') {
        if (check) return { code: 2, out: ['error: usage'] };
        check = true;
      } else if (arg === '--strict') {
        if (strict) return { code: 2, out: ['error: usage'] };
        strict = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
      continue;
    }
    positional.push(arg);
  }
  if (positional.length > 1) return { code: 2, out: ['error: usage'] };
  const patchArg = positional.length === 0 || positional[0] === '-' ? null : positional[0]!;
  let text = '';
  try {
    text = readFileSync(patchArg ?? 0, 'utf8');
  } catch {
    if (patchArg !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = splitPatch(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: EditFn[];
  try {
    if (kind === 'json') edits = parseJson(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new UsageFault('error: parse 1');
  } catch (e) {
    if (e instanceof UsageFault) return { code: 2, out: [e.text] };
    throw e;
  }
  const tree = new Tree();
  const fails: EditFault[] = [];
  for (const edit of edits) {
    const snapshot = new Map(tree.now);
    const movesLen = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFault)) throw e;
      tree.now.clear();
      for (const [k, v] of snapshot) tree.now.set(k, v);
      tree.moves.length = movesLen;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  const rows: Array<{ key: string; line: string }> = [];
  const moveOld = new Set<string>();
  const moveNew = new Set<string>();
  for (const [from, to] of tree.moves) {
    const wasFrom = tree.original(from);
    const wasTo = tree.original(to);
    const nowFrom = tree.get(from);
    const nowTo = tree.get(to);
    if (wasFrom !== null && wasTo === null && nowFrom === null && nowTo !== null) {
      rows.push({ key: to, line: `R ${from} -> ${to}` });
      moveOld.add(from);
      moveNew.add(to);
    }
  }
  for (const p of [...tree.now.keys()].sort(byteOrder)) {
    if (moveOld.has(p) || moveNew.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => byteOrder(a.key, b.key));
  if (!check) {
    for (const p of [...tree.now.keys()].sort(byteOrder)) {
      const now = tree.now.get(p)!;
      if (now === null) continue;
      if (tree.original(p) === now) continue;
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
    for (const p of [...tree.now.keys()].sort(byteOrder)) {
      const now = tree.now.get(p)!;
      if (now !== null) continue;
      if (tree.original(p) === null) continue;
      rmSync(p, { force: true });
    }
  }
  const count = rows.length;
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${count} ${count === 1 ? 'file' : 'files'}`] };
}

const trialUrl = process.env.MAKEFUN_ENV_URL;
if (trialUrl !== undefined && trialUrl !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialUrl);
} else {
  const result = runCli(process.argv.slice(2));
  writeSync(1, result.out.map((l) => `${l}\n`).join(''));
  process.exitCode = result.code;
}
