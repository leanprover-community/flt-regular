#!/usr/bin/env node

/* Independent exact-arithmetic validation of the q=3 cubic-ideal witness. */

import { readFile } from "node:fs/promises";

const raw = JSON.parse(await readFile(
  new URL("./certificate_23_prime3_cube.json", import.meta.url),
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

// Exact small-prime polynomial arithmetic checks the factor and irreducibility
// over GF(3), independently of SymPy's factorization.
const mod = (value, modulus) => {
  const result = value % modulus;
  return result < 0n ? result + modulus : result;
};
const inverseModPrime = (value, prime) => {
  const normalized = mod(value, prime);
  for (let candidate = 1n; candidate < prime; candidate += 1n) {
    if (mod(normalized * candidate, prime) === 1n) return candidate;
  }
  throw new Error(`zero has no inverse modulo ${prime}`);
};
const divRemModPrime = (numerator, denominator, prime) => {
  const remainder = trim(numerator.map((value) => mod(value, prime)));
  const divisor = trim(denominator.map((value) => mod(value, prime)));
  if (divisor.length === 0) throw new Error("division by the zero polynomial");
  const leadingInverse = inverseModPrime(divisor.at(-1), prime);
  const quotient = Array(Math.max(0, remainder.length - divisor.length + 1)).fill(0n);
  while (remainder.length >= divisor.length) {
    const shift = remainder.length - divisor.length;
    const coefficient = mod(remainder.at(-1) * leadingInverse, prime);
    quotient[shift] = coefficient;
    for (let i = 0; i < divisor.length; i += 1) {
      remainder[i + shift] = mod(remainder[i + shift] - coefficient * divisor[i], prime);
    }
    while (remainder.length > 0 && remainder.at(-1) === 0n) remainder.pop();
  }
  return [trim(quotient), remainder];
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
const q = BigInt(raw.q);
const qPoly = [q];

if (raw.p !== 23 || raw.q !== 3 || raw.residue_degree !== 11) {
  throw new Error("unexpected certificate metadata");
}
if (!equal(Phi, Array(23).fill(1n))) throw new Error("Phi is not Phi23");
const expectedF = [-1n, -1n, -1n, 1n, 1n, 0n, -1n, 0n, -1n, 0n, 0n, 1n];
if (!equal(F, expectedF)) throw new Error("unexpected pinned factor F");
if (F.length !== 12 || F.at(-1) !== 1n) throw new Error("F is not monic of degree 11");

const [, factorRemainder] = divRemModPrime(Phi, F, q);
if (factorRemainder.length !== 0) throw new Error("F does not divide Phi23 modulo 3");

// A reducible degree-11 polynomial has a nonconstant factor of degree at most
// five.  Enumerating every monic candidate requires only 3+9+27+81+243 tests.
for (let degree = 1; degree <= 5; degree += 1) {
  const count = q ** BigInt(degree);
  for (let code = 0n; code < count; code += 1n) {
    let digits = code;
    const candidate = [];
    for (let i = 0; i < degree; i += 1) {
      candidate.push(digits % q);
      digits /= q;
    }
    candidate.push(1n);
    const [, remainder] = divRemModPrime(F, candidate, q);
    if (remainder.length === 0) {
      throw new Error(`F has a monic factor of degree ${degree} modulo 3`);
    }
  }
}

const monomials = [
  pow(qPoly, 3),
  mul(pow(qPoly, 2), F),
  mul(qPoly, pow(F, 2)),
  pow(F, 3),
];
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
if (absoluteNorm !== q ** 33n || BigInt(raw.cube_norm) !== absoluteNorm) {
  throw new Error(`unexpected norm: ${norm}`);
}
if (BigInt(raw.ideal_norm) !== q ** 11n) throw new Error("unexpected ideal norm metadata");

console.log("validated q=3 prime-above-3 cube certificate");
console.log("degree(F)=11, F irreducible and F | Phi23 modulo 3");
console.log("all five Z[X] identities exact; |Norm(G)|=3^33");
