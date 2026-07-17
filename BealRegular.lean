import BealRegular.Nineteen
import BealRegular.Seventeen
import BealRegular.CubicIdealCertificate
import BealRegular.TwentyThreeBernoulli
import BealRegular.TwentyThreeDesign
import BealRegular.TwentyThreePrimeTwoCube
import BealRegular.TwentyThreePrimeThreeCube
import FltRegular.SmallNumbers.SmallNumbers

/-!
# Beal reductions backed by `flt-regular`

This companion layer imports the proved regular-prime cases of Fermat's Last
Theorem and applies them to equal exponents and to mixed exponents sharing a
common divisor. It does not assert Beal's conjecture.
-/

namespace BealRegular

/-- If an exponent satisfying FLT divides all three mixed exponents, then no
solution with nonzero bases exists. -/
theorem no_solution_of_flt_divides_exponents {A B C x y z n : ℕ}
    (hFLT : FermatLastTheoremFor n)
    (hnx : n ∣ x) (hny : n ∣ y) (hnz : n ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z := by
  obtain ⟨kx, rfl⟩ := hnx
  obtain ⟨ky, rfl⟩ := hny
  obtain ⟨kz, rfl⟩ := hnz
  intro hEq
  apply hFLT (A ^ kx) (B ^ ky) (C ^ kz)
    (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC)
  simpa only [← pow_mul, Nat.mul_comm] using hEq

/-! ## Generic regular-prime consequences -/

/-- Equal-exponent FLT for any odd prime accompanied by an upstream
`IsRegularPrime` proof. -/
theorem no_solution_equal_exponent_regular_prime {A B C p : ℕ}
    [Fact p.Prime]
    (hreg : IsRegularPrime p) (hodd : p ≠ 2)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ p + B ^ p ≠ C ^ p :=
  flt_regular hreg hodd A B C hA hB hC

/-- If an odd regular prime divides all three mixed exponents, the mixed-power
equation has no solution with nonzero bases. -/
theorem no_solution_if_regular_prime_dvd_exponents
    {A B C x y z p : ℕ} [Fact p.Prime]
    (hreg : IsRegularPrime p) (hodd : p ≠ 2)
    (hpx : p ∣ x) (hpy : p ∣ y) (hpz : p ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents
    (flt_regular hreg hodd) hpx hpy hpz hA hB hC

/-! The upstream tree contains a concrete regularity proof for `3` in
addition to the already exposed proofs for `5`, `7`, `11`, and `13`. -/

theorem no_solution_equal_exponent_three_regular {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 3 + B ^ 3 ≠ C ^ 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact no_solution_equal_exponent_regular_prime
    isRegularPrime_three (by omega) hA hB hC

theorem no_solution_if_three_regular_dvd_exponents {A B C x y z : ℕ}
    (hx : 3 ∣ x) (hy : 3 ∣ y) (hz : 3 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact no_solution_if_regular_prime_dvd_exponents
    isRegularPrime_three (by omega) hx hy hz hA hB hC

/-! ## Uniform access to every upstream small FLT case -/

/-- The upstream `FLT_small` theorem covers every exponent from 3 through 16,
including the composite exponents not listed individually below. -/
theorem no_solution_equal_exponent_small {A B C n : ℕ}
    (hn : n ∈ Finset.Icc 3 16)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ n + B ^ n ≠ C ^ n :=
  FLT_small hn A B C hA hB hC

/-- Any common mixed-exponent divisor between 3 and 16 is excluded by the
corresponding upstream `FLT_small` case. -/
theorem no_solution_if_small_dvd_exponents
    {A B C x y z n : ℕ}
    (hn : n ∈ Finset.Icc 3 16)
    (hnx : n ∣ x) (hny : n ∣ y) (hnz : n ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents (FLT_small hn)
    hnx hny hnz hA hB hC

/-! The new kernel-checked regularity certificates for `17` and `19`, together
with the exponent-three case at `18`, extend the contiguous interval. -/

/-- Fermat's Last Theorem for every exponent from `3` through `19`. -/
theorem FLT_three_through_nineteen {n : ℕ}
    (hn : n ∈ Finset.Icc 3 19) : FermatLastTheoremFor n := by
  fin_cases hn
  · exact fermatLastTheoremThree
  · exact fermatLastTheoremFour
  · exact fermatLastTheoremFive
  · exact fermatLastTheoremThree.mono (show 3 ∣ 6 by decide)
  · exact fermatLastTheoremSeven
  · exact fermatLastTheoremFour.mono (show 4 ∣ 8 by decide)
  · exact fermatLastTheoremThree.mono (show 3 ∣ 9 by decide)
  · exact fermatLastTheoremFive.mono (show 5 ∣ 10 by decide)
  · exact fermatLastTheoremEleven
  · exact fermatLastTheoremFour.mono (show 4 ∣ 12 by decide)
  · exact fermatLastTheoremThirteen
  · exact fermatLastTheoremSeven.mono (show 7 ∣ 14 by decide)
  · exact fermatLastTheoremFive.mono (show 5 ∣ 15 by decide)
  · exact fermatLastTheoremFour.mono (show 4 ∣ 16 by decide)
  · exact fermatLastTheoremSeventeen
  · exact fermatLastTheoremThree.mono (show 3 ∣ 18 by decide)
  · exact fermatLastTheoremNineteen

/-- No nonzero equal-base-exponent solution exists for any exponent in the
fully formalized interval `3 <= n <= 19`. -/
theorem no_solution_equal_exponent_through_nineteen {A B C n : ℕ}
    (hn : n ∈ Finset.Icc 3 19)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ n + B ^ n ≠ C ^ n :=
  FLT_three_through_nineteen hn A B C hA hB hC

/-- A common mixed-exponent divisor anywhere in `3..19` rules out a Beal
equation with nonzero bases. -/
theorem no_solution_if_three_through_nineteen_dvd_exponents
    {A B C x y z n : ℕ}
    (hn : n ∈ Finset.Icc 3 19)
    (hnx : n ∣ x) (hny : n ∣ y) (hnz : n ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents (FLT_three_through_nineteen hn)
    hnx hny hnz hA hB hC

/-! The composite exponents immediately above `19` are inherited from
already-formalized FLT cases: `4 | 20`, `3 | 21`, and `11 | 22`. -/

/-- Fermat's Last Theorem for every exponent from `3` through `22`. -/
theorem FLT_three_through_twentyTwo {n : ℕ}
    (hn : n ∈ Finset.Icc 3 22) : FermatLastTheoremFor n := by
  obtain ⟨h3, h22⟩ := Finset.mem_Icc.mp hn
  by_cases h19 : n ≤ 19
  · exact FLT_three_through_nineteen (Finset.mem_Icc.mpr ⟨h3, h19⟩)
  · have hnCases : n = 20 ∨ n = 21 ∨ n = 22 := by omega
    rcases hnCases with rfl | rfl | rfl
    · exact fermatLastTheoremFour.mono (show 4 ∣ 20 by decide)
    · exact fermatLastTheoremThree.mono (show 3 ∣ 21 by decide)
    · exact fermatLastTheoremEleven.mono (show 11 ∣ 22 by decide)

/-- No nonzero equal-exponent solution exists throughout the fully
formalized interval `3 <= n <= 22`. -/
theorem no_solution_equal_exponent_through_twentyTwo {A B C n : ℕ}
    (hn : n ∈ Finset.Icc 3 22)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ n + B ^ n ≠ C ^ n :=
  FLT_three_through_twentyTwo hn A B C hA hB hC

/-- A common mixed-exponent divisor anywhere in `3..22` rules out a Beal
equation with nonzero bases. -/
theorem no_solution_if_three_through_twentyTwo_dvd_exponents
    {A B C x y z n : ℕ}
    (hn : n ∈ Finset.Icc 3 22)
    (hnx : n ∣ x) (hny : n ∣ y) (hnz : n ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents (FLT_three_through_twentyTwo hn)
    hnx hny hnz hA hB hC

/-! Exponent `23` is kept assumption-explicit until either the class-group
cube certificates or Kummer's Bernoulli criterion is formalized. -/

/-- A supplied FLT theorem at `23` extends the unconditional interval
`3..22` by one. -/
theorem FLT_three_through_twentyThree_of_twentyThree
    (h23 : FermatLastTheoremFor 23) {n : ℕ}
    (hn : n ∈ Finset.Icc 3 23) : FermatLastTheoremFor n := by
  obtain ⟨h3, h23le⟩ := Finset.mem_Icc.mp hn
  by_cases h22 : n ≤ 22
  · exact FLT_three_through_twentyTwo (Finset.mem_Icc.mpr ⟨h3, h22⟩)
  · have : n = 23 := by omega
    simpa only [this] using h23

/-- Equal-exponent nonexistence throughout `3..23`, conditional only on the
explicitly supplied endpoint at `23`. -/
theorem no_solution_equal_exponent_through_twentyThree_of_twentyThree
    (h23 : FermatLastTheoremFor 23) {A B C n : ℕ}
    (hn : n ∈ Finset.Icc 3 23)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ n + B ^ n ≠ C ^ n :=
  FLT_three_through_twentyThree_of_twentyThree h23 hn A B C hA hB hC

/-- The corresponding mixed-exponent divisor theorem, with the `23` trust
boundary visible as an ordinary theorem parameter. -/
theorem no_solution_if_three_through_twentyThree_dvd_exponents_of_twentyThree
    (h23 : FermatLastTheoremFor 23) {A B C x y z n : ℕ}
    (hn : n ∈ Finset.Icc 3 23)
    (hnx : n ∣ x) (hny : n ∣ y) (hnz : n ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents
    (FLT_three_through_twentyThree_of_twentyThree h23 hn)
    hnx hny hnz hA hB hC

/-! ## Equal-exponent consequences -/

theorem no_solution_equal_exponent_five {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 5 + B ^ 5 ≠ C ^ 5 :=
  fermatLastTheoremFive A B C hA hB hC

theorem no_solution_equal_exponent_seven {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 7 + B ^ 7 ≠ C ^ 7 :=
  fermatLastTheoremSeven A B C hA hB hC

theorem no_solution_equal_exponent_eleven {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 11 + B ^ 11 ≠ C ^ 11 :=
  fermatLastTheoremEleven A B C hA hB hC

theorem no_solution_equal_exponent_thirteen {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 13 + B ^ 13 ≠ C ^ 13 :=
  fermatLastTheoremThirteen A B C hA hB hC

theorem no_solution_equal_exponent_seventeen {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 17 + B ^ 17 ≠ C ^ 17 :=
  fermatLastTheoremSeventeen A B C hA hB hC

theorem no_solution_equal_exponent_nineteen {A B C : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 19 + B ^ 19 ≠ C ^ 19 :=
  fermatLastTheoremNineteen A B C hA hB hC

/-! ## Divides-all-exponents consequences -/

theorem no_solution_if_five_dvd_exponents {A B C x y z : ℕ}
    (hx : 5 ∣ x) (hy : 5 ∣ y) (hz : 5 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents fermatLastTheoremFive hx hy hz hA hB hC

theorem no_solution_if_seven_dvd_exponents {A B C x y z : ℕ}
    (hx : 7 ∣ x) (hy : 7 ∣ y) (hz : 7 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents fermatLastTheoremSeven hx hy hz hA hB hC

theorem no_solution_if_eleven_dvd_exponents {A B C x y z : ℕ}
    (hx : 11 ∣ x) (hy : 11 ∣ y) (hz : 11 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents fermatLastTheoremEleven hx hy hz hA hB hC

theorem no_solution_if_thirteen_dvd_exponents {A B C x y z : ℕ}
    (hx : 13 ∣ x) (hy : 13 ∣ y) (hz : 13 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents fermatLastTheoremThirteen hx hy hz hA hB hC

theorem no_solution_if_seventeen_dvd_exponents {A B C x y z : ℕ}
    (hx : 17 ∣ x) (hy : 17 ∣ y) (hz : 17 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents fermatLastTheoremSeventeen hx hy hz hA hB hC

theorem no_solution_if_nineteen_dvd_exponents {A B C x y z : ℕ}
    (hx : 19 ∣ x) (hy : 19 ∣ y) (hz : 19 ∣ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ x + B ^ y ≠ C ^ z :=
  no_solution_of_flt_divides_exponents fermatLastTheoremNineteen hx hy hz hA hB hC

end BealRegular
