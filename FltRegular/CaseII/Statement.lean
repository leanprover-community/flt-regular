import FltRegular.CaseII.InductionStep

open scoped BigOperators nonZeroDivisors NumberField
open Polynomial

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))] (hreg : (p : ℕ).Coprime <| Fintype.card <| ClassGroup (𝓞 K))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

namespace FltRegular

/-- Statement of case II. -/
def CaseII.Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ [hp : Fact p.Prime] (_ : @IsRegularPrime p hp) (_ : p ≠ 2)
    (_ : a * b * c ≠ 0) (_ : ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

lemma not_exists_solution (hm : 1 ≤ m) :
  ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬((hζ.unit' : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.unit' : 𝓞 K) - 1 ∣ z') ∧
    x' ^ (p : ℕ) + y' ^ (p : ℕ) = ε₃ * (((hζ.unit' : 𝓞 K) - 1) ^ m * z') ^ (p : ℕ) := by
  induction' m, hm using Nat.le_induction with m' _ IH
  · rintro ⟨x, y, z, ε₃, hy, hz, e⟩
    exact zero_lt_one.not_le (one_le_m hp hζ e hy hz)
  · rintro ⟨x, y, z, ε₃, hy, hz, e⟩
    exact IH (exists_solution' hp hreg hζ e hy hz)

lemma not_exists_solution' :
  ¬∃ (x y z : 𝓞 K), ¬(hζ.unit' : 𝓞 K) - 1 ∣ y ∧ (hζ.unit' : 𝓞 K) - 1 ∣ z ∧ z ≠ 0 ∧
    x ^ (p : ℕ) + y ^ (p : ℕ) = z ^ (p : ℕ) := by
  letI : Fact (Nat.Prime p) := hpri
  letI : WfDvdMonoid (𝓞 K) := IsNoetherianRing.wfDvdMonoid
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  obtain ⟨m, z, hm, hz'', rfl⟩ :
    ∃ m z', 1 ≤ m ∧ ¬((hζ.unit' : 𝓞 K) - 1 ∣ z') ∧ z = ((hζ.unit' : 𝓞 K) - 1) ^ m * z' := by
    classical
    have H : multiplicity.Finite ((hζ.unit' : 𝓞 K) - 1) z := WfDvdMonoid.multiplicity_finite
      (M := 𝓞 K) hζ.zeta_sub_one_prime'.not_unit hz'
    obtain ⟨z', h⟩ := multiplicity.pow_multiplicity_dvd H
    refine ⟨_, _, ?_, ?_, h⟩
    · rwa [← PartENat.coe_le_coe, PartENat.natCast_get, ← multiplicity.pow_dvd_iff_le_multiplicity,
        pow_one]
    · intro h'
      have := mul_dvd_mul_left (((hζ.unit' : 𝓞 K) - 1) ^ Part.get (multiplicity _ z) H) h'
      rw [← pow_succ', ← h] at this
      exact multiplicity.is_greatest' H (Nat.lt_succ_self _) this
  refine not_exists_solution hp hreg hζ hm ⟨x, y, z, 1, hy, hz'', ?_⟩
  rwa [Units.val_one, one_mul]

lemma not_exists_Int_solution {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
  ¬∃ (x y z : ℤ), ¬↑p ∣ y ∧ ↑p ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  haveI : Fact (PNat.Prime ⟨p, hpri.out.pos⟩) := hpri
  haveI := CyclotomicField.isCyclotomicExtension ⟨p, hpri.out.pos⟩ ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_prim_root
    ℚ (B := (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ)) (Set.mem_singleton (⟨p, hpri.out.pos⟩ : ℕ+))
  have hodd' : (⟨p, hpri.out.pos⟩ : ℕ+) ≠ (2 : ℕ+) := by
    rwa [← PNat.coe_injective.ne_iff]
  have := fun n ↦ zeta_sub_one_dvd_Int_iff (K := CyclotomicField ⟨p, hpri.out.pos⟩ ℚ) hζ (n := n)
  simp only [PNat.mk_coe] at this
  simp_rw [← this]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  refine not_exists_solution' (K := CyclotomicField ⟨p, hpri.out.pos⟩ ℚ) hodd' ?_
    hζ ⟨x, y, z, hy, hz, ?_, ?_⟩
  · convert hreg
  · rwa [ne_eq, Int.cast_eq_zero]
  · dsimp
    simp_rw [← Int.cast_pow, ← Int.cast_add, e]

lemma not_exists_Int_solution' {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
  ¬∃ (x y z : ℤ), ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ↑p ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  refine not_exists_Int_solution hreg hodd ⟨x, y, z, ?_, hz, hz', e⟩
  intro hy
  have := dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero)
  rw [← e, add_sub_cancel] at this
  replace this := (Nat.prime_iff_prime_int.mp hpri.out).dvd_of_dvd_pow this
  apply (Nat.prime_iff_prime_int.mp hpri.out).not_unit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, this]

lemma Int.gcd_left_comm (a b c : ℤ) : Int.gcd a (Int.gcd b c) = Int.gcd b (Int.gcd a c) := by
  rw [← Int.gcd_assoc, ← Int.gcd_assoc, Int.gcd_comm a b]

/-- CaseII. -/
theorem caseII {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseII : ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro e
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨a0, b0⟩, c0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two hpri.out hodd
  obtain (hab|hc) := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd caseII
  obtain (ha|hb) := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
  · refine not_exists_Int_solution' hreg hodd ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
    · simp only [← hgcd, Finset.mem_singleton, Finset.mem_insert, neg_inj, Finset.gcd_insert, id_eq,
        ← Int.coe_gcd, Int.gcd_neg_left, Nat.cast_inj, ← insert_emptyc_eq, Finset.gcd_empty,
        Int.gcd_left_comm _ a]
    · rwa [dvd_neg]
    · rwa [ne_eq, neg_eq_zero]
    · simp [hodd'.neg_pow, ← e]
  · refine not_exists_Int_solution' hreg hodd ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
    · simp only [← hgcd, Finset.mem_singleton, Finset.mem_insert, neg_inj, Finset.gcd_insert, id_eq,
        ← Int.coe_gcd, Int.gcd_neg_left, Nat.cast_inj, ← insert_emptyc_eq, Finset.gcd_empty,
        Int.gcd_left_comm _ c]
    · rwa [dvd_neg]
    · rwa [ne_eq, neg_eq_zero]
    · simp [hodd'.neg_pow, ← e]
  · exact not_exists_Int_solution' hreg hodd ⟨a, b, c, hgcd, hc, c0, e⟩

end FltRegular
