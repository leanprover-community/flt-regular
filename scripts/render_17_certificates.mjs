#!/usr/bin/env node

/* Render Sage's exact p = 17 polynomial witnesses as bounded Lean modules. */

import { readFile, writeFile } from "node:fs/promises";

const inputPath = new URL("./certificates_17.json", import.meta.url);
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

const chunkSize = 10;
const chunks = [];
for (let index = 0; index < certificates.length; index += chunkSize) {
  chunks.push(certificates.slice(index, index + chunkSize));
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
  const orderOneParameter = certificate.order === 1
    ? `\n    (hmod : ${certificate.p} % 17 = 1)`
    : "";
  const orderProof = certificate.order === 1
    ? `  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod`
    : `  · rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
    have hn : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
    fin_cases hn <;> decide +revert`;
  return `set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_${certificate.p} [Fact (Nat.Prime ${certificate.p})]
    (hpn : ${certificate.p} ≠ 17)${orderOneParameter} : SeventeenCertificate ${certificate.p} hpn := by
  dsimp only [SeventeenCertificate]
${lets}
  let d := ${certificate.order}
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
${orderProof}
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring`;
}

const arithmeticSource = `import BealRegular.SeventeenBounds

/-! Symbolic arithmetic shared by the independently compiled p = 17 certificates. -/

namespace SeventeenCertificateArithmetic

theorem orderOf_unitOfCoprime_eq_one_of_mod_eq_one {p : ℕ} [Fact p.Prime]
    (hpn : p ≠ 17) (hmod : p % 17 = 1) :
    orderOf (ZMod.unitOfCoprime p (uff Nat.prime_seventeen hpn)) = 1 := by
  rw [orderOf_eq_one_iff]
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime, Units.val_one]
  exact (ZMod.natCast_eq_natCast_iff' p 1 17).2 (by simpa using hmod)

end SeventeenCertificateArithmetic
`;
await writeGenerated(new URL("SeventeenCertificateArithmetic.lean", outputDirectory), arithmeticSource);

const baseSource = `import BealRegular.SeventeenCertificateArithmetic
import FltRegular.FltRegular
import FltRegular.NumberTheory.RegularPrimes
import Mathlib.NumberTheory.FLT.Basic

/-! Shared statement for independently compiled regular-prime-17 certificates. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

def SeventeenCertificate (p : ℕ) [Fact p.Prime] (hpn : p ≠ 17) : Prop :=
  ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
    P.Monic ∧
      orderOf (ZMod.unitOfCoprime p (uff Nat.prime_seventeen hpn)) = P.natDegree ∧
      P * Q + p * A = cyclotomic 17 ℤ ∧
      (p = G * Qp + Rp * cyclotomic 17 ℤ ∧
        P = G * QP + RP * cyclotomic 17 ℤ ∧ G = C1 * P + C2 * p)
`;
await writeGenerated(new URL("SeventeenCertificateBase.lean", outputDirectory), baseSource);

for (let index = 0; index < chunks.length; index += 1) {
  const suffix = String(index).padStart(2, "0");
  const first = chunks[index][0].p;
  const last = chunks[index][chunks[index].length - 1].p;
  const source = `import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes ${first} through ${last}. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

${chunks[index].map(certificateTheorem).join("\n\n")}
`;
  await writeGenerated(new URL(`SeventeenCertificates${suffix}.lean`, outputDirectory), source);
}

const imports = chunks.map((_, index) =>
  `import BealRegular.SeventeenCertificates${String(index).padStart(2, "0")}`
).join("\n");
const alternatives = certificates.map(() => "rfl").join(" | ");
const dispatch = certificates.map(({ p, order }) =>
  order === 1
    ? `    · right\n      exact seventeenCertificate_${p} hpn (by norm_num)`
    : `    · right\n      exact seventeenCertificate_${p} hpn`
).join("\n");

const mainSource = `import BealRegular.SeventeenBounds
${imports}

/-!
# The regular prime 17

The ${certificates.length} exact polynomial certificates imported above prove that the ring of
integers of the seventeenth cyclotomic field is a PID. Sage discovered the witnesses; Lean's
kernel checks every displayed polynomial identity and finite order calculation.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {17} ℚ K]

set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
variable (K) in
theorem Rat.seventeen_pid : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 17
  rw [M17]
  intro p hple hp hpn
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hmem : p ∈ exceptionalPrimesSeventeen
  · simp only [exceptionalPrimesSeventeen, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ${alternatives}
${dispatch}
  · left
    exact log_lt_orderOf_seventeen_of_not_mem hp hpn (Finset.mem_Icc.mp hple).2 hmem

set_option backward.isDefEq.respectTransparency false in
theorem isRegularPrime_seventeen :
    haveI : Fact (Nat.Prime 17) := ⟨Nat.prime_seventeen⟩
    IsRegularPrime 17 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.seventeen_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremSeventeen : FermatLastTheoremFor 17 :=
  @flt_regular 17 ⟨Nat.prime_seventeen⟩ isRegularPrime_seventeen (by omega)
`;
await writeGenerated(new URL("Seventeen.lean", outputDirectory), mainSource);

console.log(`rendered ${certificates.length} certificates in ${chunks.length} chunks`);
