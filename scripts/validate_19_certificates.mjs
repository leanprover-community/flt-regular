#!/usr/bin/env node

/* Independently check every exact identity emitted by the p = 19 generator. */

import { readFile, readdir } from "node:fs/promises";

const inputPath = new URL("./certificates_19.json", import.meta.url);
const leanDirectory = new URL("../BealRegular/", import.meta.url);
const payload = JSON.parse(await readFile(inputPath, "utf8"));
const boundsSource = await readFile(
  new URL("NineteenBoundsData.lean", leanDirectory), "utf8");
const bound = BigInt(payload.bound);
const phi19 = Array(19).fill(1n);

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function polynomial(coefficients) {
  return coefficients.map(BigInt);
}

function normalize(coefficients) {
  const result = [...coefficients];
  while (result.length > 1 && result.at(-1) === 0n) result.pop();
  return result.length === 0 ? [0n] : result;
}

function add(left, right) {
  const result = Array(Math.max(left.length, right.length)).fill(0n);
  for (let index = 0; index < result.length; index += 1) {
    result[index] = (left[index] ?? 0n) + (right[index] ?? 0n);
  }
  return normalize(result);
}

function multiply(left, right) {
  const result = Array(left.length + right.length - 1).fill(0n);
  for (let i = 0; i < left.length; i += 1) {
    for (let j = 0; j < right.length; j += 1) result[i + j] += left[i] * right[j];
  }
  return normalize(result);
}

function scale(scalar, value) {
  return normalize(value.map((coefficient) => scalar * coefficient));
}

function equal(left, right) {
  const a = normalize(left);
  const b = normalize(right);
  return a.length === b.length && a.every((coefficient, index) => coefficient === b[index]);
}

function isPrime(value) {
  if (value < 2) return false;
  if (value % 2 === 0) return value === 2;
  for (let divisor = 3; divisor * divisor <= value; divisor += 2) {
    if (value % divisor === 0) return false;
  }
  return true;
}

function orderModulo19(value) {
  let power = value % 19;
  for (let order = 1; order <= 18; order += 1) {
    if (power === 1) return order;
    power = (power * value) % 19;
  }
  throw new Error(`${value} is not a unit modulo 19`);
}

function pow(base, exponent) {
  let result = 1n;
  for (let index = 0; index < exponent; index += 1) result *= base;
  return result;
}

assert(payload.bound === 105933, `unexpected bound ${payload.bound}`);
assert(payload.class_number === 1, `unexpected Sage class number ${payload.class_number}`);
assert(payload.certificates.length === 558,
  `expected 558 certificates, got ${payload.certificates.length}`);

const expectedPrimes = [];
for (let prime = 2; prime <= payload.bound; prime += 1) {
  if (!isPrime(prime) || prime === 19) continue;
  const order = orderModulo19(prime);
  if (pow(BigInt(prime), order) <= bound) expectedPrimes.push(prime);
}

const actualPrimes = payload.certificates.map(({ p }) => p);
assert(JSON.stringify(actualPrimes) === JSON.stringify(expectedPrimes),
  "certificate primes are not exactly the exceptional primes below the bound");

function primesInLeanDefinition(name) {
  const match = boundsSource.match(
    new RegExp(`def ${name} : Finset ℕ :=\\s*\\[([\\s\\S]*?)\\]\\.toFinset`),
  );
  assert(match, `could not find Lean definition ${name}`);
  return [...match[1].matchAll(/\d+/g)].map(([value]) => Number(value));
}

const expectedNonSplitPrimes = payload.certificates
  .filter(({ order }) => order !== 1).map(({ p }) => p);
const expectedSplitPrimes = payload.certificates
  .filter(({ order }) => order === 1).map(({ p }) => p);
assert(JSON.stringify(primesInLeanDefinition("exceptionalNonSplitPrimesNineteen")) ===
  JSON.stringify(expectedNonSplitPrimes),
  "Lean's non-split exceptional-prime list does not match the certificates");

const maximumClassificationK = Math.floor((payload.bound - 1) / 19);
const splitDataChunkSize = 250;
const splitDataRanges = [];
for (let lower = 0; lower <= maximumClassificationK; lower += splitDataChunkSize) {
  splitDataRanges.push([lower,
    Math.min(lower + splitDataChunkSize - 1, maximumClassificationK)]);
}
const localSplitPrimes = [];
const splitDataSliceSizes = [];
for (let index = 0; index < splitDataRanges.length; index += 1) {
  const suffix = String(index).padStart(2, "0");
  const localName = `exceptionalSplitPrimesNineteen_${suffix}`;
  const localPrimes = primesInLeanDefinition(localName);
  const [lower, upper] = splitDataRanges[index];
  const expectedLocalPrimes = expectedSplitPrimes.filter((prime) => {
    const k = (prime - 1) / 19;
    return lower <= k && k <= upper;
  });
  assert(JSON.stringify(localPrimes) === JSON.stringify(expectedLocalPrimes),
    `${localName} does not exactly match its 250-candidate data range`);
  localSplitPrimes.push(...localPrimes);
  splitDataSliceSizes.push(localPrimes.length);
}
assert(JSON.stringify(localSplitPrimes) === JSON.stringify(expectedSplitPrimes),
  "the ordered local split-prime slices do not flatten to all 552 split certificates");
const combinedExceptionalPrimes = [...expectedNonSplitPrimes, ...localSplitPrimes]
  .sort((left, right) => left - right);
assert(JSON.stringify(combinedExceptionalPrimes) === JSON.stringify(actualPrimes),
  "the union of split and non-split Lean data is not all 558 exceptional primes");
assert(boundsSource.includes("def exceptionalSplitPrimesNineteen : Finset ℕ :=") &&
  boundsSource.includes("def exceptionalPrimesNineteen : Finset ℕ :=\n" +
    "  exceptionalNonSplitPrimesNineteen ∪ exceptionalSplitPrimesNineteen"),
  "Lean's generated global exceptional Finsets are not wired from the split/non-split data");

const classificationChunkSize = 125;
const classificationRanges = [];
for (let lower = 0; lower <= maximumClassificationK; lower += classificationChunkSize) {
  classificationRanges.push([lower,
    Math.min(lower + classificationChunkSize - 1, maximumClassificationK)]);
}
const expectedClassificationFiles = classificationRanges.map((_, index) =>
  `NineteenPrimeClassification${String(index).padStart(2, "0")}.lean`);
const actualClassificationFiles = (await readdir(leanDirectory))
  .filter((name) => /^NineteenPrimeClassification\d{2}\.lean$/.test(name))
  .sort();
assert(JSON.stringify(actualClassificationFiles) === JSON.stringify(expectedClassificationFiles),
  "generated classifier filenames do not match the expected 125-candidate partition");

const aggregatorSource = await readFile(
  new URL("NineteenPrimeClassification.lean", leanDirectory), "utf8");
for (let index = 0; index < classificationRanges.length; index += 1) {
  const suffix = String(index).padStart(2, "0");
  const filename = expectedClassificationFiles[index];
  const source = await readFile(new URL(filename, leanDirectory), "utf8");
  const rangeMatch = source.match(/Finset\.Icc (\d+) (\d+)/);
  const [lower, upper] = classificationRanges[index];
  const splitSliceIndex = Math.floor(lower / splitDataChunkSize);
  const splitSliceSuffix = String(splitSliceIndex).padStart(2, "0");
  const localName = `exceptionalSplitPrimesNineteen_${splitSliceSuffix}`;
  assert(source.startsWith("import BealRegular.NineteenBoundsData\n"),
    `${filename} does not independently import NineteenBoundsData`);
  assert(rangeMatch && Number(rangeMatch[1]) === classificationRanges[index][0] &&
    Number(rangeMatch[2]) === classificationRanges[index][1],
  `${filename} has the wrong candidate interval`);
  assert(aggregatorSource.includes(`import BealRegular.NineteenPrimeClassification${suffix}`),
    `classifier aggregator does not import ${suffix}`);
  assert(source.includes(`19 * k + 1 ∈ ${localName}`),
    `${filename} does not classify into its local Finset`);
  assert(aggregatorSource.includes(`prime_mem_exceptionalSplitPrimesNineteen_${suffix} k`),
    `classifier aggregator does not use ${suffix}`);
  assert(aggregatorSource.includes(
    `exceptionalSplitPrimesNineteen_${splitSliceSuffix}_mem hlocal`),
    `classifier aggregator does not structurally lift ${suffix}`);
}

const boundsProofSource = await readFile(new URL("NineteenBounds.lean", leanDirectory), "utf8");
assert(boundsProofSource.includes("import BealRegular.NineteenPrimeClassification\n"),
  "NineteenBounds does not import the generated classifier aggregator");
assert(boundsProofSource.includes("prime_mem_exceptionalSplitPrimesNineteen_of_k_le hk hprime"),
  "NineteenBounds does not use the generated classifier composition theorem");
const mainSource = await readFile(new URL("Nineteen.lean", leanDirectory), "utf8");
assert(mainSource.includes("prime_mem_exceptionalSplitPrimesNineteen_of_mod_eq_one") &&
  mainSource.includes(
    "simp only [exceptionalSplitPrimesNineteen, Finset.mem_union] at hmem"),
"Nineteen's split dispatcher is not staged through the split global Finset");
assert(mainSource.includes("letI : Fact p.Prime := ⟨hp⟩"),
  "Nineteen's dispatcher does not expose the PID theorem's primality proof as a Fact");
for (let index = 0; index < splitDataRanges.length; index += 1) {
  const suffix = String(index).padStart(2, "0");
  const localName = `exceptionalSplitPrimesNineteen_${suffix}`;
  assert(mainSource.includes(
    `simp only [${localName}, List.mem_toFinset, List.mem_cons,`),
  `Nineteen's split dispatcher does not locally destructure ${localName}`);
}
for (const certificate of payload.certificates) {
  const dispatch = certificate.order === 1
    ? `      · right\n        exact nineteenCertificate_${certificate.p} hpn hmod`
    : `      · right\n        exact nineteenCertificate_${certificate.p} hpn`;
  assert(mainSource.includes(dispatch),
    `Nineteen's dispatcher does not invoke certificate ${certificate.p} in its local branch`);
}
assert(mainSource.includes(
  "exact log_lt_orderOf_nineteen_of_mod_ne_one hp hpn\n" +
    "        (Finset.mem_Icc.mp hple).2 hmod hmem"),
"Nineteen's non-split fallback does not project the PID-bound membership proof");

const distribution = new Map();
let maximumCoefficientDigits = 0;
for (const certificate of payload.certificates) {
  const prefix = `p = ${certificate.p}`;
  const order = orderModulo19(certificate.p);
  assert(certificate.order === order,
    `${prefix}: stored order ${certificate.order}, computed ${order}`);
  distribution.set(order, (distribution.get(order) ?? 0) + 1);

  const values = Object.fromEntries(
    ["P", "Q", "A", "G", "Qp", "Rp", "QP", "RP", "C1", "C2"]
      .map((name) => [name, polynomial(certificate[name])]),
  );
  for (const coefficients of Object.values(values)) {
    for (const coefficient of coefficients) {
      const digits = (coefficient < 0n ? -coefficient : coefficient).toString().length;
      maximumCoefficientDigits = Math.max(maximumCoefficientDigits, digits);
    }
  }

  assert(values.P.length - 1 === order, `${prefix}: degree(P) is not the order`);
  assert(values.P.at(-1) === 1n, `${prefix}: P is not monic`);
  assert(equal(add(multiply(values.P, values.Q), scale(BigInt(certificate.p), values.A)), phi19),
    `${prefix}: P*Q + p*A != Phi_19`);
  assert(equal(add(multiply(values.G, values.Qp), multiply(values.Rp, phi19)),
    [BigInt(certificate.p)]), `${prefix}: G*Qp + Rp*Phi_19 != p`);
  assert(equal(add(multiply(values.G, values.QP), multiply(values.RP, phi19)), values.P),
    `${prefix}: G*QP + RP*Phi_19 != P`);
  assert(equal(add(multiply(values.C1, values.P), scale(BigInt(certificate.p), values.C2)),
    values.G), `${prefix}: C1*P + p*C2 != G`);
}

console.log(JSON.stringify({
  bound: payload.bound,
  certificates: payload.certificates.length,
  firstPrime: actualPrimes[0],
  lastPrime: actualPrimes.at(-1),
  orderDistribution: Object.fromEntries([...distribution].sort(([a], [b]) => a - b)),
  maximumCoefficientDigits,
  classifierModules: classificationRanges.length,
  classifiedCandidates: maximumClassificationK + 1,
  splitDataSlices: splitDataRanges.length,
  splitDataSliceSizes,
}));
