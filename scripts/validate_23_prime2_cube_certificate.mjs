#!/usr/bin/env node

/* Independent exact-arithmetic validation of the q=2 cubic-ideal witness. */

import { readFile } from "node:fs/promises";

const raw = JSON.parse(await readFile(
  new URL("./certificate_23_prime2_cube.json", import.meta.url),
  "utf8",
));

const poly = (name) => raw[name].map(BigInt);
const trim = (a) => {
  const result = [...a];
  while (result.length > 0 && result.at(-1) === 0n) result.pop();
  return result;
};
const add = (...values) => {
  const length = Math.max(0, ...values.map((value) => value.length));
  return trim(Array.from({ length }, (_, i) =>
    values.reduce((sum, value) => sum + (value[i] ?? 0n), 0n)));
};
const neg = (a) => a.map((value) => -value);
const mul = (a, b) => {
  if (a.length === 0 || b.length === 0) return [];
  const result = Array(a.length + b.length - 1).fill(0n);
  for (let i = 0; i < a.length; i += 1) {
    for (let j = 0; j < b.length; j += 1) result[i + j] += a[i] * b[j];
  }
  return trim(result);
};
const pow = (a, exponent) => {
  let result = [1n];
  let base = a;
  let n = exponent;
  while (n > 0) {
    if (n % 2 === 1) result = mul(result, base);
    base = mul(base, base);
    n = Math.floor(n / 2);
  }
  return result;
};
const equal = (a, b) => {
  const aa = trim(a);
  const bb = trim(b);
  return aa.length === bb.length && aa.every((value, i) => value === bb[i]);
};
const assertPoly = (description, actual, expected) => {
  if (!equal(actual, expected)) throw new Error(`failed identity: ${description}`);
};

const divRemMonic = (numerator, denominator) => {
  const remainder = trim(numerator);
  const divisor = trim(denominator);
  if (divisor.length === 0 || divisor.at(-1) !== 1n) {
    throw new Error("divRemMonic requires a nonzero monic divisor");
  }
  const quotient = Array(Math.max(0, remainder.length - divisor.length + 1)).fill(0n);
  while (remainder.length >= divisor.length) {
    const shift = remainder.length - divisor.length;
    const coefficient = remainder.at(-1);
    quotient[shift] = coefficient;
    for (let i = 0; i < divisor.length; i += 1) {
      remainder[i + shift] -= coefficient * divisor[i];
    }
    while (remainder.length > 0 && remainder.at(-1) === 0n) remainder.pop();
  }
  return [trim(quotient), remainder];
};

// Tiny GF(2) implementation used to check that F is an irreducible monic
// degree-11 factor of Phi23 modulo 2.
const toBits = (a) => a.reduce(
  (bits, coefficient, i) => bits | ((coefficient & 1n) << BigInt(i)),
  0n,
);
const bitDegree = (a) => a === 0n ? -1 : a.toString(2).length - 1;
const bitRem = (numerator, denominator) => {
  let result = numerator;
  const degree = bitDegree(denominator);
  while (bitDegree(result) >= degree) {
    result ^= denominator << BigInt(bitDegree(result) - degree);
  }
  return result;
};

const determinantBareiss = (matrix) => {
  const a = matrix.map((row) => [...row]);
  let sign = 1n;
  let previous = 1n;
  for (let k = 0; k < a.length - 1; k += 1) {
    let pivot = k;
    while (pivot < a.length && a[pivot][k] === 0n) pivot += 1;
    if (pivot === a.length) return 0n;
    if (pivot !== k) {
      [a[pivot], a[k]] = [a[k], a[pivot]];
      sign = -sign;
    }
    const pivotValue = a[k][k];
    for (let i = k + 1; i < a.length; i += 1) {
      for (let j = k + 1; j < a.length; j += 1) {
        const numerator = a[i][j] * pivotValue - a[i][k] * a[k][j];
        if (numerator % previous !== 0n) throw new Error("non-exact Bareiss division");
        a[i][j] = numerator / previous;
      }
    }
    previous = pivotValue;
  }
  return sign * a.at(-1).at(-1);
};

const Phi = poly("Phi");
const F = poly("F");
const G = poly("G");
const q = [BigInt(raw.q)];

if (raw.p !== 23 || raw.q !== 2 || raw.residue_degree !== 11) {
  throw new Error("unexpected certificate metadata");
}
if (!equal(Phi, Array(23).fill(1n))) throw new Error("Phi is not Phi23");
if (F.length !== 12 || F.at(-1) !== 1n) throw new Error("F is not monic of degree 11");

const phiBits = toBits(Phi);
const fBits = toBits(F);
if (bitRem(phiBits, fBits) !== 0n) throw new Error("F does not divide Phi23 modulo 2");
for (let degree = 1; degree <= 5; degree += 1) {
  for (let low = 0n; low < (1n << BigInt(degree)); low += 1n) {
    const candidate = (1n << BigInt(degree)) | low;
    if (bitRem(fBits, candidate) === 0n) {
      throw new Error(`F has a factor of degree ${degree} modulo 2`);
    }
  }
}

const monomials = [pow(q, 3), mul(pow(q, 2), F), mul(q, pow(F, 2)), pow(F, 3)];
for (let i = 0; i < 4; i += 1) {
  assertPoly(
    `q^(3-${i}) F^${i} = G Q${i} + Phi R${i}`,
    monomials[i],
    add(mul(G, poly(`Q${i}`)), mul(Phi, poly(`R${i}`))),
  );
}
assertPoly(
  "G = C0 q^3 + C1 q^2 F + C2 q F^2 + C3 F^3 + Phi R4",
  G,
  add(...monomials.map((monomial, i) => mul(poly(`C${i}`), monomial)),
    mul(Phi, poly("R4"))),
);

// The determinant of multiplication by G on Z[X]/(Phi23) is Norm(G).
const multiplicationMatrix = Array.from({ length: 22 }, () => Array(22).fill(0n));
for (let column = 0; column < 22; column += 1) {
  const shifted = Array(column).fill(0n).concat(G);
  const [, remainder] = divRemMonic(shifted, Phi);
  for (let row = 0; row < 22; row += 1) multiplicationMatrix[row][column] = remainder[row] ?? 0n;
}
const norm = determinantBareiss(multiplicationMatrix);
const absoluteNorm = norm < 0n ? -norm : norm;
if (absoluteNorm !== 2n ** 33n || BigInt(raw.cube_norm) !== absoluteNorm) {
  throw new Error(`unexpected norm: ${norm}`);
}
if (BigInt(raw.ideal_norm) !== 2n ** 11n) throw new Error("unexpected ideal norm metadata");

console.log("validated q=2 prime-above-2 cube certificate");
console.log("degree(F)=11, F irreducible and F | Phi23 modulo 2");
console.log("all five Z[X] identities exact; |Norm(G)|=2^33");
