// Matrix Inverse Race: the rules, shared by the page and the server.
// The page uses them to play; the server uses them to replay a submitted game and
// confirm its turn count, so a score can't be made up.
// server/matrix.mjs must stay an exact copy of this file (run `npm run sync` in local/).

// ---------- Exact fractions ----------
const absB = x => (x < 0n ? -x : x);
const gcd = (a, b) => { a = absB(a); b = absB(b); while (b) [a, b] = [b, a % b]; return a; };
export class F {
  constructor(n, d = 1n) {
    n = BigInt(n); d = BigInt(d);
    if (d === 0n) throw new Error("Division by zero");
    if (d < 0n) { n = -n; d = -d; }
    const g = gcd(n, d) || 1n;
    this.n = n / g; this.d = d / g;
  }
  add(o) { return new F(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { return new F(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { return new F(this.n * o.n, this.d * o.d); }
  div(o) { return new F(this.n * o.d, this.d * o.n); }
  neg() { return new F(-this.n, this.d); }
  abs() { return new F(absB(this.n), this.d); }
  get zero() { return this.n === 0n; }
  get one() { return this.n === 1n && this.d === 1n; }
  eq(o) { return this.n === o.n && this.d === o.d; }
  toString() { return this.d === 1n ? `${this.n}` : `${this.n}/${this.d}`; }
  static parse(s) {
    s = String(s).trim().replace(/[−–]/g, "-").replace(/^\((.*)\)$/, "$1").trim();
    let m = s.match(/^([+-]?\d+)(?:\/([+-]?\d+))?$/);
    if (m) { if (m[2] !== undefined && BigInt(m[2]) === 0n) return null; return new F(m[1], m[2] ?? 1); }
    m = s.match(/^([+-]?)(\d*)\.(\d+)$/);
    if (m) return new F(BigInt((m[1] || "") + ((m[2] || "0") + m[3])), 10n ** BigInt(m[3].length));
    return null;
  }
}
export const Z = new F(0), ONE = new F(1);

// ---------- Matrices ----------
export const MAX_N = 6;
export const toF = rows => rows.map(r => r.map(x => (x instanceof F ? x : F.parse(x))));
export const codeOf = A => `${A.length}:` + A.map(r => r.map(String).join(",")).join(";");
export const augment = A => A.map((r, i) => [...r, ...r.map((_, j) => (i === j ? ONE : Z))]);
export const isIdentity = M => M.every((r, i) => r.every((x, j) => x.eq(i === j ? ONE : Z)));
export const leftHalf = M => M.map(r => r.slice(0, M.length));
export const rightHalf = M => M.map(r => r.slice(M.length));
export const multiply = (A, B) => A.map(r => B[0].map((_, j) => r.reduce((acc, x, k) => acc.add(x.mul(B[k][j])), Z)));

export function det(A) {
  const n = A.length, M = A.map(r => r.slice()); let d = ONE;
  for (let c = 0; c < n; c++) {
    let p = -1; for (let r = c; r < n; r++) if (!M[r][c].zero) { p = r; break; }
    if (p < 0) return Z;
    if (p !== c) { [M[c], M[p]] = [M[p], M[c]]; d = d.neg(); }
    d = d.mul(M[c][c]);
    for (let r = c + 1; r < n; r++) { const k = M[r][c].div(M[c][c]); M[r] = M[r].map((x, j) => x.sub(k.mul(M[c][j]))); }
  }
  return d;
}
export const isSingular = A => det(A).zero;
// Index of a row whose left half is all zeros (the proof that A has no inverse), or -1.
export const zeroRow = M => M.findIndex(r => r.slice(0, M.length).every(x => x.zero));

// Matrices with no inverse are allowed: spotting one is part of the game.
// Reads a square matrix from rows of strings or numbers, or from a code like "3:1,2,3;0,1,4;5,6,0".
// Returns {A} or {err}. Entries are kept small so nobody can make the server do huge arithmetic.
export function readMatrix(input) {
  let rows = input;
  if (typeof input === "string") {
    const raw = input.trim(), m = raw.match(/^(\d+)\s*:\s*([\s\S]+)$/);
    rows = m ? m[2].split(";").map(r => r.split(",")) : raw.split(/\n+/).map(r => r.trim()).filter(Boolean).map(r => r.split(/[\s,]+/));
  }
  if (!Array.isArray(rows) || !rows.every(Array.isArray)) return { err: "Send the matrix as a list of rows." };
  const n = rows.length;
  if (n < 2 || n > MAX_N) return { err: `Use a square matrix from 2×2 to ${MAX_N}×${MAX_N}.` };
  if (rows.some(r => r.length !== n)) return { err: `Every row needs ${n} numbers to make a square matrix.` };
  const A = rows.map(r => r.map(x => F.parse(String(x).trim())));
  if (A.some(r => r.some(x => !x))) return { err: "Some entries aren't numbers. Use forms like 3, -2, 1/2 or 0.5." };
  if (A.some(r => r.some(x => absB(x.n) > 1000n || x.d > 1000n))) return { err: "Keep entries between -1000 and 1000, with denominators up to 1000." };
  return { A };
}

// ---------- Random challenges ----------
// "whole": built from integer row operations, so the determinant is ±1 and the inverse has whole numbers.
// "fractions": random entries with a determinant other than ±1, so the inverse needs fractions.
export function randomMatrix(n, kind = "whole", rnd = Math.random) {
  const ri = (lo, hi) => lo + Math.floor(rnd() * (hi - lo + 1));
  for (let tries = 0; tries < 5000; tries++) {
    let A;
    if (kind === "whole") {
      A = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0)));
      for (let k = 0; k < 2 * n + 1; k++) {
        const i = ri(0, n - 1); let j = ri(0, n - 2); if (j >= i) j++;
        if (rnd() < 0.15) [A[i], A[j]] = [A[j], A[i]];
        else { const c = (rnd() < 0.5 ? -1 : 1) * ri(1, 2); A[i] = A[i].map((x, col) => x + c * A[j][col]); }
      }
    } else A = Array.from({ length: n }, () => Array.from({ length: n }, () => ri(-5, 9)));
    if (A.flat().some(x => Math.abs(x) > 12)) continue;
    const off = A.flatMap((r, i) => r.filter((_, j) => i !== j));
    if (off.filter(x => x !== 0).length < off.length / 2) continue;   // nearly diagonal is too easy
    const d = det(toF(A));
    if (d.zero || (kind === "fractions" && (d.abs().one || absB(d.n) > 60n))) continue;
    return A;
  }
  return null;
}
// A matrix with no inverse: one row is a small combination of the others.
export function randomSingular(n, rnd = Math.random) {
  const ri = (lo, hi) => lo + Math.floor(rnd() * (hi - lo + 1));
  for (let tries = 0; tries < 5000; tries++) {
    const A = Array.from({ length: n }, () => Array.from({ length: n }, () => ri(-4, 7)));
    const i = ri(0, n - 1), others = [...Array(n).keys()].filter(r => r !== i);
    const j = others[ri(0, others.length - 1)], k = others[ri(0, others.length - 1)];
    const c1 = (rnd() < 0.5 ? -1 : 1) * ri(1, 2), c2 = k !== j ? (rnd() < 0.5 ? -1 : 1) * ri(1, 2) : 0;
    A[i] = A[j].map((x, col) => c1 * x + c2 * A[k][col]);
    if (A.flat().some(x => Math.abs(x) > 12) || A[i].every(x => x === 0)) continue;
    if (det(toF(A)).zero) return A;
  }
  return null;
}

// A challenge's id comes from its matrix, so the same matrix is always the same challenge
// and shares one leaderboard, whoever creates it first.
export async function challengeId(A) {
  const bytes = new Uint8Array(await globalThis.crypto.subtle.digest("SHA-256", new TextEncoder().encode(codeOf(A))));
  const abc = "abcdefghjkmnpqrstuvwxyz23456789";
  return Array.from(bytes.slice(0, 8), b => abc[b % abc.length]).join("");
}

// ---------- Row operations ----------
// op: {type:"combo", t, a:F, terms:[{s, b:F}, ...]}  means  Rt <- a*Rt + b1*Rs1 + b2*Rs2 + ...  (up to N-1 other rows)
//     {type:"swap", i, j}                              means  Ri <-> Rj
// A turn's operations all read the matrix as it stood at the start of the turn, so a row can be changed
// and its original values still used to change another row. Each row may change once per turn, and the
// turn as a whole must be reversible: R1 <- R1 + R2 together with R2 <- R2 + R1 would make two equal rows.
export const touched = op => (op.type === "swap" ? [op.i, op.j] : [op.t]);
export const feeds = op => (op.type === "combo" ? op.terms.map(x => x.s) : []);

export function validate(op, pending, n) {
  if (pending.length >= n - 1) return `A turn holds at most ${n - 1} operation${n - 1 > 1 ? "s" : ""}. Play this turn first.`;
  const inRange = r => Number.isInteger(r) && r >= 0 && r < n;
  if (op.type === "swap") {
    if (!inRange(op.i) || !inRange(op.j)) return `Rows go from R1 to R${n}.`;
    if (op.i === op.j) return "Pick two different rows to swap.";
  } else if (op.type === "combo") {
    if (!inRange(op.t) || op.terms.some(x => !inRange(x.s))) return `Rows go from R1 to R${n}.`;
    if (op.a.zero) return `The multiplier on R${op.t + 1} can't be 0.`;
    if (op.terms.some(x => x.s === op.t)) return `R${op.t + 1} is already on the right once. Add other rows to it.`;
    if (new Set(op.terms.map(x => x.s)).size < op.terms.length) return "Use each other row at most once.";
    if (op.terms.some(x => x.b.zero)) return "A multiplier of 0 adds nothing. Remove that row instead.";
    if (!op.terms.length && op.a.one) return "That leaves the row unchanged.";
  } else return "Unknown operation.";
  const ch = new Set(pending.flatMap(touched));
  for (const r of touched(op)) if (ch.has(r)) return `R${r + 1} already changes this turn.`;
  if (det(turnMatrix([...pending, op], n)).zero)
    return "Together with this turn's other operations, that would make the matrix lose its inverse. Play it next turn instead.";
  return null;
}

// Applies one turn: every operation reads the rows as they were before the turn.
export function apply(M, ops) {
  const out = M.map(r => r.slice());
  for (const op of ops) {
    if (op.type === "swap") { out[op.i] = M[op.j].slice(); out[op.j] = M[op.i].slice(); }
    else out[op.t] = M[op.t].map((x, k) => op.terms.reduce((v, { s, b }) => v.add(M[s][k].mul(b)), x.mul(op.a)));
  }
  return out;
}
// The turn written as one matrix T (new rows = T × old rows). The turn is reversible exactly when det(T) ≠ 0.
export function turnMatrix(ops, n) {
  return apply(Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? ONE : Z))), ops);
}

function coefTxt(f) { // magnitude-only coefficient for display ("" for 1)
  const a = f.abs();
  if (a.one) return "";
  return a.d === 1n ? `${a.n}` : `(${a.n}/${a.d})`;
}
// Display form, e.g. "R2 ← R2 − 2R1". parseOp reads it back, which is how turns travel to the server.
export function opText(op) {
  if (op.type === "swap") return `R${op.i + 1} ↔ R${op.j + 1}`;
  let s = `R${op.t + 1} ← ${op.a.n < 0n ? "−" : ""}${coefTxt(op.a)}R${op.t + 1}`;
  for (const { s: r, b } of op.terms) s += ` ${b.n < 0n ? "−" : "+"} ${coefTxt(b)}R${r + 1}`;
  return s;
}

// Reads "R2 <- R2 - 2R1", "R1 <-> R3", "R3 <- 1/2 R3", "R1 = R1 + 3R2" (and the display form above).
export function parseOp(txt, n) {
  if (typeof txt !== "string" || txt.length > 80) return { err: "Try a form like R2 <- R2 - 2R1 or R1 <-> R3." };
  let s = txt.replace(/\s+/g, "").replace(/[−–]/g, "-").replace(/[·*]/g, "").replace(/↔|<-->|<->/g, "<>")
    .replace(/←|<--|<-|:=|=/g, "<-").toUpperCase();
  const row = k => { const r = parseInt(k, 10) - 1; return r >= 0 && r < n ? r : null; };
  let m = s.match(/^(?:SWAP)?R(\d+)(?:<>|,)R(\d+)$/);
  if (m) { const i = row(m[1]), j = row(m[2]); if (i === null || j === null) return { err: `Rows go from R1 to R${n}.` }; return { op: { type: "swap", i, j } }; }
  m = s.match(/^R(\d+)<-(.+)$/);
  if (!m) return { err: "Try a form like R2 <- R2 - 2R1 or R1 <-> R3." };
  const t = row(m[1]); if (t === null) return { err: `Rows go from R1 to R${n}.` };
  const terms = [...m[2].matchAll(/([+-]?)\(?([+-]?[\d./]*)\)?R(\d+)/g)];
  if (!terms.length || terms.map(x => x[0]).join("") !== m[2]) return { err: "I couldn't read the right-hand side. Try R2 <- R2 - 2R1." };
  let a = null; const others = [];
  for (const [, sign, c, rr] of terms) {
    const r = row(rr); if (r === null) return { err: `Rows go from R1 to R${n}.` };
    let k = c === "" || c === "+" ? ONE : c === "-" ? new F(-1) : F.parse(c);
    if (!k) return { err: `“${c}” isn't a number.` };
    if (sign === "-") k = k.neg();
    if (r === t) { if (a) return { err: `R${t + 1} appears twice.` }; a = k; }
    else { if (others.some(x => x.s === r)) return { err: `R${r + 1} appears twice.` }; others.push({ s: r, b: k }); }
  }
  if (!a) return { err: `The new R${t + 1} has to include R${t + 1} itself (to keep the matrix invertible).` };
  return { op: { type: "combo", t, a, terms: others } };
}

// ---------- Verifying a finished game ----------
export const MAX_TURNS = 100;
export const WRONG_CLAIM = "wrong-claim";   // a turn spent claiming "no inverse" on a matrix that has one
// turns: array of turns, each an array of operation strings, or WRONG_CLAIM.
// outcome: "inverse" (A times the right side is I) or "none" (a row on the left is all zeros).
// Returns {turns} or {err}.
export function verifyGame(A, turns, outcome) {
  const n = A.length;
  if (!Array.isArray(turns)) return { err: "No turns were sent." };
  if (turns.length > MAX_TURNS) return { err: `A game can have at most ${MAX_TURNS} turns.` };
  let M = augment(A);
  const singular = isSingular(A);
  for (const [k, turn] of turns.entries()) {
    if (turn === WRONG_CLAIM) { if (singular) return { err: `Turn ${k + 1}: that claim would have been right.` }; continue; }
    if (!Array.isArray(turn) || !turn.length) return { err: `Turn ${k + 1} is empty.` };
    const ops = [];
    for (const txt of turn) {
      const p = parseOp(txt, n);
      if (p.err) return { err: `Turn ${k + 1}: ${p.err}` };
      const e = validate(p.op, ops, n);
      if (e) return { err: `Turn ${k + 1}: ${e}` };
      ops.push(p.op);
    }
    M = apply(M, ops);
  }
  if (outcome === "none") { if (zeroRow(M) < 0) return { err: "Those turns don't end with a row of zeros on the left." }; }
  else if (outcome === "inverse") { if (!isIdentity(multiply(A, rightHalf(M)))) return { err: "Those turns don't end with the inverse." }; }
  else return { err: "Say how the game ended." };
  return { turns: turns.length };
}
