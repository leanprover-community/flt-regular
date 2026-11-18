module

public import FltRegular.NumberTheory.RegularPrimes
import FltRegular.CaseII.InductionStep
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

@[expose] public section

open scoped nonZeroDivisors NumberField
open Polynomial

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

namespace FltRegular

include hp hreg in
lemma not_exists_solution {m : ℕ} (hm : 1 ≤ m) :
  ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬((hζ.toInteger : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
    x' ^ p + y' ^ p = ε₃ * (((hζ.toInteger : 𝓞 K) - 1) ^ m * z') ^ p := by
  induction m, hm using Nat.le_induction with
  | base =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact zero_lt_one.not_ge (one_le_m hp hζ e hy hz)
  | succ m' _ IH =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact IH (exists_solution' hp hζ e hy hz hreg)

include hp hreg in
lemma not_exists_solution' : ¬∃ (x y z : 𝓞 K), ¬(hζ.toInteger : 𝓞 K) - 1 ∣ y ∧
    (hζ.toInteger : 𝓞 K) - 1 ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  obtain ⟨m, z', hz'', rfl⟩ := WfDvdMonoid.max_power_factor hz' hζ.zeta_sub_one_prime'.irreducible
  refine not_exists_solution (m := m) hp hreg hζ
    (Nat.pos_of_ne_zero fun hm ↦ hz'' (by simpa [hm] using hz)) ⟨x, y, z', 1, hy, hz'', ?_⟩
  rwa [Units.val_one, one_mul]

lemma not_exists_Int_solution {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ), ¬↑p ∣ y ∧ ↑p ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  simp_rw [← IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'
    (K := CyclotomicField p ℚ) p hζ]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  exact not_exists_solution' (K := CyclotomicField p ℚ) hodd hreg hζ
    ⟨x, y, z, hy, hz, mod_cast hz', mod_cast e⟩

lemma not_exists_Int_solution' {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ), ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ↑p ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  refine not_exists_Int_solution hreg hodd ⟨x, y, z, fun hy ↦ ?_, hz, hz', e⟩
  have hpri' := Nat.prime_iff_prime_int.mp hpri.out
  have hx := hpri'.dvd_of_dvd_pow (add_sub_cancel_right (x ^ p) (y ^ p) ▸ e ▸
    dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero))
  exact hpri'.not_isUnit <|
    isUnit_iff_dvd_one.mpr (hgcd ▸ Finset.dvd_gcd_iff.mpr (by simp [hx, hy, hz]))

/-- Case II of Fermat's Last Theorem for regular primes. -/
theorem caseII {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseII : ↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro e
  have hodd' := hpri.out.odd_of_ne_two hodd
  have hpri' := Nat.prime_iff_prime_int.mp hpri.out
  obtain hab | hc := hpri'.dvd_or_dvd caseII
  · obtain ha | hb := hpri'.dvd_or_dvd hab
    · refine not_exists_Int_solution' hreg hodd
        ⟨b, -c, -a, ?_, dvd_neg.mpr ha, by grind, by simp [hodd'.neg_pow, ← e]⟩
      simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
        ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
    · refine not_exists_Int_solution' hreg hodd
        ⟨-c, a, -b, ?_, dvd_neg.mpr hb, by grind, by simp [hodd'.neg_pow, ← e]⟩
      simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
        ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
  · exact not_exists_Int_solution' hreg hodd ⟨a, b, c, hgcd, hc, by grind, e⟩

end FltRegular
