#!/usr/bin/env node

/* Render Sage's exact p = 19 polynomial witnesses as parallel Lean modules. */

import { readFile, writeFile } from "node:fs/promises";

const inputPath = new URL("./certificates_19.json", import.meta.url);
const outputDirectory = new URL("../BealRegular/", import.meta.url);
const { certificates } = JSON.parse(await readFile(inputPath, "utf8"));

async function writeGenerated(url, source) {
  try {
    if (await readFile(url, "utf8") === source) return;
  } catch (error) {
    if (error.code !== "ENOENT") throw error;
  }
  await writeFile(url, source);
}

const chunkSize = 50;
const chunks = [];
for (let index = 0; index < certificates.length; index += chunkSize) {
  chunks.push(certificates.slice(index, index + chunkSize));
}

const maximumClassificationK = 5575;
const splitDataChunkSize = 250;
const splitDataRanges = [];
for (let lower = 0; lower <= maximumClassificationK; lower += splitDataChunkSize) {
  splitDataRanges.push([lower, Math.min(lower + splitDataChunkSize - 1,
    maximumClassificationK)]);
}
const classificationChunkSize = 125;
const classificationRanges = [];
for (let lower = 0; lower <= maximumClassificationK; lower += classificationChunkSize) {
  classificationRanges.push([lower, Math.min(lower + classificationChunkSize - 1,
    maximumClassificationK)]);
}

function naturalFinsetDefinition(name, values) {
  const lines = [];
  let line = "  [";
  values.forEach((value, index) => {
    const token = `${value}${index + 1 === values.length ? "" : ","}`;
    if (`${line} ${token}`.length > 100 && line !== "  [") {
      lines.push(line);
      line = `    ${token}`;
    } else {
      line += `${line === "  [" ? "" : " "}${token}`;
    }
  });
  lines.push(`${line}].toFinset`);
  return `def ${name} : Finset ℕ :=\n${lines.join("\n")}`;
}

function polynomial(coefficients) {
  if (coefficients.length === 0 || coefficients.every((coefficient) => BigInt(coefficient) === 0n)) {
    return "0";
  }
  const terms = [];
  for (let exponent = coefficients.length - 1; exponent >= 0; exponent -= 1) {
    const coefficient = BigInt(coefficients[exponent]);
    if (coefficient === 0n) continue;
    const magnitude = coefficient < 0n ? -coefficient : coefficient;
    const variable = exponent === 0 ? "" : exponent === 1 ? "X" : `X^${exponent}`;
    const body = exponent === 0
      ? `${magnitude}`
      : magnitude === 1n ? variable : `${magnitude}*${variable}`;
    terms.push({ negative: coefficient < 0n, body });
  }
  return terms.map(({ negative, body }, index) => {
    if (index === 0) return negative ? `-${body}` : body;
    return negative ? ` - ${body}` : ` + ${body}`;
  }).join("");
}

function wrappedLet(name, coefficients) {
  const expression = polynomial(coefficients);
  if (expression.length <= 92) return `  let ${name} : ℤ[X] := ${expression}`;
  const pieces = expression.split(/ (?=[+-] )/);
  const lines = [];
  let line = `  let ${name} : ℤ[X] :=`;
  for (const piece of pieces) {
    if (`${line} ${piece}`.length > 104 && line !== `  let ${name} : ℤ[X] :=`) {
      lines.push(line);
      line = `    ${piece}`;
    } else {
      line += ` ${piece}`;
    }
  }
  lines.push(line);
  return lines.join("\n");
}

function certificateTheorem(certificate) {
  const names = ["P", "Q", "A", "G", "Qp", "Rp", "QP", "RP", "C1", "C2"];
  const lets = names.map((name) => wrappedLet(name, certificate[name])).join("\n");
  const splitPrimeParameter = certificate.order === 1
    ? `\n    (hmod : ${certificate.p} % 19 = 1)`
    : "";
  const orderProof = certificate.order === 1
    ? `  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod`
    : `  · rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
    have hn : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
    fin_cases hn <;> decide +revert`;
  return `set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_${certificate.p} [Fact (Nat.Prime ${certificate.p})]
    (hpn : ${certificate.p} ≠ 19)${splitPrimeParameter} :
    NineteenCertificate ${certificate.p} hpn := by
  dsimp only [NineteenCertificate]
${lets}
  let d := ${certificate.order}
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
${orderProof}
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring`;
}

const exceptionalNonSplitPrimes = certificates
  .filter(({ order }) => order !== 1)
  .map(({ p }) => p);
const splitCertificates = certificates.filter(({ order }) => order === 1);
const splitPrimeSlices = splitDataRanges.map(([lower, upper]) =>
  splitCertificates
    .filter(({ p }) => lower <= (p - 1) / 19 && (p - 1) / 19 <= upper)
    .map(({ p }) => p)
);
const splitSliceNames = splitDataRanges.map((_, index) =>
  `exceptionalSplitPrimesNineteen_${String(index).padStart(2, "0")}`);
const splitSliceDefinitions = splitSliceNames.map((name, index) =>
  naturalFinsetDefinition(name, splitPrimeSlices[index])).join("\n\n");
const splitPrimeUnion = splitSliceNames.reduceRight((union, name) =>
  union === "" ? name : `${name} ∪ (${union})`, "");
function splitSubsetWitness(index) {
  let witness = index + 1 === splitSliceNames.length ? "hp" : "Or.inl hp";
  for (let depth = 0; depth < index; depth += 1) witness = `Or.inr (${witness})`;
  return witness;
}
const splitSubsetTheorems = splitSliceNames.map((name, index) => {
  const suffix = String(index).padStart(2, "0");
  return `theorem exceptionalSplitPrimesNineteen_${suffix}_mem {p : ℕ}
    (hp : p ∈ ${name}) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact ${splitSubsetWitness(index)}`;
}).join("\n\n");
const boundsDataSource = `import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.longLine false

/-! Finite prime data shared by the independently compiled p = 19 bound checks. -/

open Finset

/-! The exceptional primes that do not split completely modulo 19. The primes
\`7\` and \`11\` have order three; the other four have order two. -/

${naturalFinsetDefinition("exceptionalNonSplitPrimesNineteen", exceptionalNonSplitPrimes)}

/-! The 552 split exceptional primes, partitioned by the classifier's k ranges. -/

${splitSliceDefinitions}

def exceptionalSplitPrimesNineteen : Finset ℕ :=
  ${splitPrimeUnion}

/-! All 558 exceptional primes, split and non-split. -/

def exceptionalPrimesNineteen : Finset ℕ :=
  exceptionalNonSplitPrimesNineteen ∪ exceptionalSplitPrimesNineteen

/-! Structural inclusions used to lift each inexpensive local classification. -/

${splitSubsetTheorems}
`;
await writeGenerated(new URL("NineteenBoundsData.lean", outputDirectory), boundsDataSource);

for (let index = 0; index < classificationRanges.length; index += 1) {
  const suffix = String(index).padStart(2, "0");
  const [lower, upper] = classificationRanges[index];
  const splitSliceIndex = Math.floor(lower / splitDataChunkSize);
  const source = `import BealRegular.NineteenBoundsData
import Mathlib.Tactic.IntervalCases

/-! Exhaustive p = 19 split-prime classification for k in [${lower}, ${upper}]. -/

set_option maxHeartbeats 0 in
-- Checks every candidate in this bounded interval by explicit arithmetic cases.
set_option maxRecDepth 20000 in
theorem prime_mem_exceptionalSplitPrimesNineteen_${suffix} :
    ∀ k ∈ Finset.Icc ${lower} ${upper}, (19 * k + 1).Prime →
      19 * k + 1 ∈ ${splitSliceNames[splitSliceIndex]} := by
  intro k hk hp
  simp only [Finset.mem_Icc] at hk
  obtain ⟨hk${lower}, hk${upper}⟩ := hk
  interval_cases k
  all_goals solve
    | norm_num at hp
    | norm_num [${splitSliceNames[splitSliceIndex]}]
`;
  await writeGenerated(
    new URL(`NineteenPrimeClassification${suffix}.lean`, outputDirectory), source);
}

const classificationImports = classificationRanges.map((_, index) =>
  `import BealRegular.NineteenPrimeClassification${String(index).padStart(2, "0")}`
).join("\n");
const classificationRangePropositions = classificationRanges.map(([lower, upper]) =>
  `(${lower} ≤ k ∧ k ≤ ${upper})`
).join(" ∨\n      ");
const classificationAlternatives = classificationRanges.map(() => "hrange").join(" | ");
const classificationDispatch = classificationRanges.map((_, index) => {
  const suffix = String(index).padStart(2, "0");
  const splitSliceIndex = Math.floor(classificationRanges[index][0] / splitDataChunkSize);
  const splitSliceSuffix = String(splitSliceIndex).padStart(2, "0");
  return `  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_${suffix} k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_${splitSliceSuffix}_mem hlocal`;
}).join("\n");
const classificationAggregatorSource = `${classificationImports}

/-! Composition of the independently compiled p = 19 split-prime classifiers. -/

set_option linter.style.longLine false in
set_option maxRecDepth 20000 in
theorem prime_mem_exceptionalSplitPrimesNineteen_of_k_le {k : ℕ}
    (hk : k ≤ ${maximumClassificationK}) (hprime : (19 * k + 1).Prime) :
    19 * k + 1 ∈ exceptionalSplitPrimesNineteen := by
  have hranges :
      ${classificationRangePropositions} := by
    omega
  rcases hranges with ${classificationAlternatives}
${classificationDispatch}
`;
await writeGenerated(
  new URL("NineteenPrimeClassification.lean", outputDirectory), classificationAggregatorSource);

const baseSource = `module

public import BealRegular.NineteenCertificateArithmetic
import FltRegular.FltRegular
public import FltRegular.NumberTheory.RegularPrimes
public import Mathlib.NumberTheory.FLT.Basic

/-! Shared statement for independently compiled regular-prime-19 certificates. -/

@[expose] public section

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

def NineteenCertificate (p : ℕ) [Fact p.Prime] (hpn : p ≠ 19) : Prop :=
  ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
    P.Monic ∧
      orderOf (ZMod.unitOfCoprime p (uff NineteenCertificateArithmetic.prime_nineteen hpn)) =
        P.natDegree ∧
      P * Q + p * A = cyclotomic 19 ℤ ∧
      (p = G * Qp + Rp * cyclotomic 19 ℤ ∧
        P = G * QP + RP * cyclotomic 19 ℤ ∧ G = C1 * P + C2 * p)
`;
await writeGenerated(new URL("NineteenCertificateBase.lean", outputDirectory), baseSource);

for (let index = 0; index < chunks.length; index += 1) {
  const suffix = String(index).padStart(2, "0");
  const first = chunks[index][0].p;
  const last = chunks[index][chunks[index].length - 1].p;
  const source = `import BealRegular.NineteenCertificateBase

/-! Exact polynomial certificates for p = 19, rational primes ${first} through ${last}. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

${chunks[index].map(certificateTheorem).join("\n\n")}
`;
  await writeGenerated(new URL(`NineteenCertificates${suffix}.lean`, outputDirectory), source);
}

const imports = chunks.map((_, index) =>
  `import BealRegular.NineteenCertificates${String(index).padStart(2, "0")}`
).join("\n");
const splitSliceAlternatives = splitSliceNames.map((_, index) =>
  `hlocal${String(index).padStart(2, "0")}`).join(" | ");
const splitSliceDispatch = splitPrimeSlices.map((primes, index) => {
  const suffix = String(index).padStart(2, "0");
  const localName = splitSliceNames[index];
  const localAlternatives = primes.map(() => "rfl").join(" | ");
  const certificateDispatch = primes.map((p) =>
    `      · right\n        exact nineteenCertificate_${p} hpn hmod`
  ).join("\n");
  return `    · simp only [${localName}, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal${suffix}
      rcases hlocal${suffix} with ${localAlternatives}
${certificateDispatch}`;
}).join("\n");
const nonSplitCertificates = certificates.filter(({ order }) => order !== 1);
const nonSplitAlternatives = nonSplitCertificates.map(() => "rfl").join(" | ");
const nonSplitDispatch = nonSplitCertificates.map(({ p }) =>
  `      · right\n        exact nineteenCertificate_${p} hpn`
).join("\n");
const mainSource = `import BealRegular.NineteenBounds
${imports}

/-!
# The regular prime 19

The ${certificates.length} exact polynomial certificates imported above prove that the ring of
integers of the nineteenth cyclotomic field is a PID. Sage discovered the witnesses; Lean's
kernel checks every displayed polynomial identity and finite order calculation.
-/

@[expose] public section

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {19} ℚ K]

set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.style.longLine false in
set_option maxHeartbeats 0 in
-- Dispatches all 558 independently checked exceptional-prime certificates.
set_option maxRecDepth 30000 in
variable (K) in
theorem Rat.nineteen_pid : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 19
  rw [M19]
  intro p hple hp hpn
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hmod : p % 19 = 1
  · have hmem := prime_mem_exceptionalSplitPrimesNineteen_of_mod_eq_one hp
      (Finset.mem_Icc.mp hple).2 hmod
    simp only [exceptionalSplitPrimesNineteen, Finset.mem_union] at hmem
    rcases hmem with ${splitSliceAlternatives}
${splitSliceDispatch}
  · by_cases hmem : p ∈ exceptionalNonSplitPrimesNineteen
    · simp only [exceptionalNonSplitPrimesNineteen, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with ${nonSplitAlternatives}
${nonSplitDispatch}
    · left
      exact log_lt_orderOf_nineteen_of_mod_ne_one hp hpn
        (Finset.mem_Icc.mp hple).2 hmod hmem

set_option backward.isDefEq.respectTransparency false in
theorem isRegularPrime_nineteen :
    haveI : Fact (Nat.Prime 19) := ⟨Nat.prime_nineteen⟩
    IsRegularPrime 19 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.nineteen_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremNineteen : FermatLastTheoremFor 19 :=
  @flt_regular 19 ⟨Nat.prime_nineteen⟩ isRegularPrime_nineteen (by omega)
`;
await writeGenerated(new URL("Nineteen.lean", outputDirectory), mainSource);

const auditSource = `import BealRegular.Nineteen

/-! Kernel axiom audit for the regular-prime-19 certificate. -/

#print axioms Rat.nineteen_pid
#print axioms isRegularPrime_nineteen
#print axioms fermatLastTheoremNineteen
`;
await writeGenerated(new URL("NineteenAudit.lean", outputDirectory), auditSource);

console.log(`rendered ${certificates.length} certificates in ${chunks.length} chunks`);
