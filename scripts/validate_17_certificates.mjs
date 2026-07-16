#!/usr/bin/env node

/* Independently validate the serialized p = 17 certificate corpus with BigInt arithmetic. */

import { readFile } from "node:fs/promises";

const inputPath = new URL("./certificates_17.json", import.meta.url);
const data = JSON.parse(await readFile(inputPath, "utf8"));
const { bound, class_number: classNumber, certificates } = data;

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function normalize(polynomial) {
  const result = polynomial.map(BigInt);
  while (result.length > 0 && result.at(-1) === 0n) result.pop();
  return result;
}

function add(left, right) {
  const result = Array.from({ length: Math.max(left.length, right.length) }, () => 0n);
  for (let index = 0; index < result.length; index += 1) {
    result[index] = (left[index] ?? 0n) + (right[index] ?? 0n);
  }
  return normalize(result);
}

function scale(scalar, polynomial) {
  return normalize(polynomial.map((coefficient) => scalar * coefficient));
}

function multiply(left, right) {
  if (left.length === 0 || right.length === 0) return [];
  const result = Array.from({ length: left.length + right.length - 1 }, () => 0n);
  for (let i = 0; i < left.length; i += 1) {
    for (let j = 0; j < right.length; j += 1) result[i + j] += left[i] * right[j];
  }
  return normalize(result);
}

function equal(left, right) {
  const a = normalize(left);
  const b = normalize(right);
  return a.length === b.length && a.every((coefficient, index) => coefficient === b[index]);
}

function constant(value) {
  return value === 0n ? [] : [value];
}

function isPrime(value) {
  if (!Number.isSafeInteger(value) || value < 2) return false;
  if (value % 2 === 0) return value === 2;
  for (let divisor = 3; divisor * divisor <= value; divisor += 2) {
    if (value % divisor === 0) return false;
  }
  return true;
}

function multiplicativeOrderMod17(value) {
  const residue = value % 17;
  assert(residue !== 0, `${value} is not a unit modulo 17`);
  let power = 1;
  for (let order = 1; order <= 16; order += 1) {
    power = (power * residue) % 17;
    if (power === 1) return order;
  }
  throw new Error(`failed to find the order of ${value} modulo 17`);
}

function powerAtMostBound(base, exponent, maximum) {
  let power = 1n;
  for (let index = 0; index < exponent; index += 1) {
    power *= BigInt(base);
    if (power > BigInt(maximum)) return false;
  }
  return true;
}

assert(bound === 13254, `unexpected bound ${bound}`);
assert(classNumber === 1, `unexpected class number ${classNumber}`);
assert(certificates.length === 103, `expected 103 certificates, got ${certificates.length}`);

const expectedPrimes = [];
for (let prime = 2; prime <= bound; prime += 1) {
  if (prime === 17 || !isPrime(prime)) continue;
  const order = multiplicativeOrderMod17(prime);
  if (powerAtMostBound(prime, order, bound)) expectedPrimes.push(prime);
}

const serializedPrimes = certificates.map(({ p }) => p);
assert(new Set(serializedPrimes).size === serializedPrimes.length, "duplicate certificate prime");
assert(serializedPrimes.every((prime, index) => index === 0 || serializedPrimes[index - 1] < prime),
  "certificate primes are not strictly increasing");
assert(JSON.stringify(serializedPrimes) === JSON.stringify(expectedPrimes),
  "serialized certificate-prime list differs from independent enumeration");

const phi = Array.from({ length: 17 }, () => 1n);
const orderCounts = new Map();

for (const certificate of certificates) {
  const { p, order } = certificate;
  assert(isPrime(p), `${p} is not prime`);
  assert(p !== 17, "17 must not appear in its own certificate list");
  assert(order === multiplicativeOrderMod17(p), `wrong order for ${p}`);
  assert(powerAtMostBound(p, order, bound), `${p} is not exceptional at bound ${bound}`);

  const polynomials = Object.fromEntries(
    ["P", "Q", "A", "G", "Qp", "Rp", "QP", "RP", "C1", "C2"]
      .map((name) => [name, normalize(certificate[name])]),
  );
  const { P, Q, A, G, Qp, Rp, QP, RP, C1, C2 } = polynomials;
  const primePolynomial = constant(BigInt(p));

  assert(P.length === order + 1, `P has wrong degree for ${p}`);
  assert(P.at(-1) === 1n, `P is not monic for ${p}`);
  assert(equal(add(multiply(P, Q), scale(BigInt(p), A)), phi),
    `cyclotomic factor identity failed for ${p}`);
  assert(equal(add(multiply(G, Qp), multiply(Rp, phi)), primePolynomial),
    `p/G Bezout identity failed for ${p}`);
  assert(equal(add(multiply(G, QP), multiply(RP, phi)), P),
    `P/G Bezout identity failed for ${p}`);
  assert(equal(add(multiply(C1, P), scale(BigInt(p), C2)), G),
    `G/(P,p) Bezout identity failed for ${p}`);

  orderCounts.set(order, (orderCounts.get(order) ?? 0) + 1);
}

console.log(JSON.stringify({
  bound,
  classNumber,
  certificates: certificates.length,
  firstPrime: serializedPrimes[0],
  lastPrime: serializedPrimes.at(-1),
  orderCounts: Object.fromEntries([...orderCounts].sort(([left], [right]) => left - right)),
}));
