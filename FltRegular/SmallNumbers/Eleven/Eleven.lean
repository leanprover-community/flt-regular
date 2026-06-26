module

import FltRegular.SmallNumbers.Cyclotomic
import FltRegular.SmallNumbers.OrderOf
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

@[expose] public section

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

instance Nat.fact_prime_eleven : Fact (Nat.Prime 11) :=
  ⟨prime_eleven⟩

lemma crazy11 : ⌊(4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691)⌋₊ = 58 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * 48558) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 58 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * 48559) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ 58 + 1 := by norm_num

variable [IsCyclotomicExtension {11} ℚ K]

theorem M11 : ⌊(M K)⌋₊ = 58 := by
  rw [discr_prime 11 K, IsCyclotomicExtension.finrank (n := 11) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 11, totient_prime
      Nat.prime_eleven]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy11

theorem cyclotomic_11 : cyclotomic 11 ℤ =
    X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
variable (K) in
theorem Rat.eleven_pid : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 11
  rw [M11, cyclotomic_11]
  intro p hple hp hpn
  fin_cases hple
  any_goals norm_num at hp
  on_goal 5 => simp at hpn
  on_goal 8 =>
    right
    let P : ℤ[X] := X + 5
    let d := 1
    let Q : ℤ[X] :=
      X^9 + 19*X^8 + 21*X^7 + 11*X^6 + 15*X^5 + 18*X^4 + 3*X^3 +
        9*X^2 + 2*X + 14
    let A : ℤ[X] :=
      -X^9 - 5*X^8 - 5*X^7 - 3*X^6 - 4*X^5 - 4*X^4 - X^3 - 2*X^2 -
        X - 3
    let G : ℤ[X] := -X^8 - X^7 - X^6 - X^5 - X^4 - X^3 - X - 1
    let Qp : ℤ[X] :=
      17*X^9 + X^8 + 12*X^7 + 3*X^6 + 2*X^5 + 7*X^4 + 5*X^3 +
        15*X^2 + 11*X + 8
    let Rp : ℤ[X] :=
      17*X^7 + X^6 + 12*X^5 + 3*X^4 + 2*X^3 + 7*X^2 - 12*X + 31
    let QP : ℤ[X] := 3*X^9 + 2*X^7 + X^4 + X^3 + 3*X^2 + 2*X + 1
    let RP : ℤ[X] := 3*X^7 + 2*X^5 + X^2 - 2*X + 6
    let C1 : ℤ[X] :=
      -X^7 + 4*X^6 - 21*X^5 + 104*X^4 - 521*X^3 + 2604*X^2 -
        13020*X + 65099
    let C2 : ℤ[X] := -14152
    use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  all_goals
    left
    simp
    norm_num
    refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
    have := Finset.mem_Icc.mpr ⟨hipos, hi⟩
    fin_cases this <;> norm_num
