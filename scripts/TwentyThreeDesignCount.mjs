#!/usr/bin/env node

// Reproduce the scale estimate in TwentyThreeDesign.md.  This is research
// plumbing only: none of these JavaScript calculations are imported by Lean.

const cyclotomicPrime = 23;
const degree = cyclotomicPrime - 1;
const complexPlaces = degree / 2;

function integerSqrt(n) {
  if (n < 0n) throw new RangeError("integer square root of a negative number");
  if (n < 2n) return n;
  let x = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
  while (true) {
    const next = (x + n / x) / 2n;
    if (next >= x) return x;
    x = next;
  }
}

let factorial = 1n;
for (let n = 2n; n <= BigInt(degree); n += 1n) factorial *= n;

const scale = 10n ** 30n;
// floor(pi * 10^30); the next integer is the corresponding strict upper bound.
const piFloor = 3_141_592_653_589_793_238_462_643_383_279n;
const piCeil = piFloor + 1n;
const sqrt23Floor = integerSqrt(23n * scale ** 2n);
const sqrt23Ceil = sqrt23Floor + 1n;

// M = (4/pi)^11 * 22!/22^22 * 23^10 * sqrt(23).
// Fixed-point intervals for pi and sqrt(23) give rational lower/upper bounds.
function minkowskiNumerator(sqrt23Scaled) {
  return (
    4n ** BigInt(complexPlaces) *
    factorial *
    23n ** 10n *
    sqrt23Scaled *
    scale ** BigInt(complexPlaces - 1)
  );
}

function minkowskiDenominator(piScaled) {
  return piScaled ** BigInt(complexPlaces) * 22n ** 22n;
}

const lowerNumerator = minkowskiNumerator(sqrt23Floor);
const lowerDenominator = minkowskiDenominator(piCeil);
const upperNumerator = minkowskiNumerator(sqrt23Ceil);
const upperDenominator = minkowskiDenominator(piFloor);
const lowerFloor = lowerNumerator / lowerDenominator;
const upperFloor = upperNumerator / upperDenominator;

if (lowerFloor !== 9_324_406n || upperFloor !== 9_324_406n) {
  throw new Error(`Minkowski interval does not determine the expected floor: ${lowerFloor}..${upperFloor}`);
}

// For prime p, |disc(Q(zeta_p))| = p^(p-2).
const minkowski =
  (4 / Math.PI) ** complexPlaces *
  (Number(factorial) / degree ** degree) *
  cyclotomicPrime ** ((cyclotomicPrime - 2) / 2);
const bound = Number(lowerFloor);

if (Math.floor(minkowski) !== bound) {
  throw new Error(`unexpected Minkowski floor: ${bound}`);
}

const isPrime = new Uint8Array(bound + 1);
isPrime.fill(1, 2);
for (let p = 2; p * p <= bound; p += 1) {
  if (!isPrime[p]) continue;
  for (let n = p * p; n <= bound; n += p) isPrime[n] = 0;
}

function orderMod23(q) {
  const residue = q % cyclotomicPrime;
  let power = residue;
  let order = 1;
  while (power !== 1) {
    power = (power * residue) % cyclotomicPrime;
    order += 1;
  }
  return order;
}

function powerAtMostBound(base, exponent) {
  const bigintBase = BigInt(base);
  const bigintBound = BigInt(bound);
  let value = 1n;
  for (let n = 0; n < exponent; n += 1) {
    value *= bigintBase;
    if (value > bigintBound) return false;
  }
  return true;
}

const byOrder = new Map();
for (let q = 2; q <= bound; q += 1) {
  if (!isPrime[q] || q === cyclotomicPrime) continue;
  const order = orderMod23(q);
  if (!powerAtMostBound(q, order)) continue;
  byOrder.set(order, (byOrder.get(order) ?? 0) + 1);
}

const total = [...byOrder.values()].reduce((sum, count) => sum + count, 0);
const result = {
  minkowski,
  floor: bound,
  floorCertifiedByFixedPointInterval: lowerFloor === upperFloor,
  relevantPrimeCountExcluding23: total,
  countsByResidueDegree: Object.fromEntries([...byOrder.entries()].sort((a, b) => a[0] - b[0])),
};

const expected = JSON.stringify({ 1: 28_262, 2: 19, 11: 2 });
if (total !== 28_283 || JSON.stringify(result.countsByResidueDegree) !== expected) {
  throw new Error(`unexpected count: ${JSON.stringify(result)}`);
}

console.log(JSON.stringify(result, null, 2));
