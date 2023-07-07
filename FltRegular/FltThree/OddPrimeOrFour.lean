/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

! This file was ported from Lean 3 source module main
-/
import Mathlib.Data.Int.Parity
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Prime

/-- Being equal to `4` or odd. -/
def OddPrimeOrFour (z : ℤ) : Prop :=
  z = 4 ∨ Prime z ∧ Odd z
#align odd_prime_or_four OddPrimeOrFour

theorem OddPrimeOrFour.ne_zero {z : ℤ} (h : OddPrimeOrFour z) : z ≠ 0 :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · norm_num
  · exact h.ne_zero
#align odd_prime_or_four.ne_zero OddPrimeOrFour.ne_zero

theorem OddPrimeOrFour.ne_one {z : ℤ} (h : OddPrimeOrFour z) : z ≠ 1 :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · norm_num
  · exact h.ne_one
#align odd_prime_or_four.ne_one OddPrimeOrFour.ne_one

theorem OddPrimeOrFour.one_lt_abs {z : ℤ} (h : OddPrimeOrFour z) : 1 < abs z :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · rw [Int.abs_eq_natAbs]
    norm_num
  · rw [Int.abs_eq_natAbs]
    rw [Int.prime_iff_natAbs_prime] at h
    norm_cast
    exact h.one_lt
#align odd_prime_or_four.one_lt_abs OddPrimeOrFour.one_lt_abs

theorem OddPrimeOrFour.not_unit {z : ℤ} (h : OddPrimeOrFour z) : ¬IsUnit z :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · rw [isUnit_iff_dvd_one]
    norm_num
  · exact h.not_unit
#align odd_prime_or_four.not_unit OddPrimeOrFour.not_unit

theorem OddPrimeOrFour.abs {z : ℤ} (h : OddPrimeOrFour z) : OddPrimeOrFour (abs z) :=
  by
  obtain rfl | ⟨hp, ho⟩ := h
  · left
    rw [abs_eq_self]
    norm_num
  · right
    exact ⟨hp.abs, odd_abs.mpr ho⟩
#align odd_prime_or_four.abs OddPrimeOrFour.abs

theorem OddPrimeOrFour.exists_and_dvd {n : ℤ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ OddPrimeOrFour p :=
  by
  lift n to ℕ using (zero_lt_two.trans n2).le
  norm_cast  at n2
  obtain ⟨k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · refine' ⟨4, ⟨2 ^ (k - 2), _⟩, Or.inl rfl⟩
    norm_cast
    calc
      2 ^ k = 2 ^ 2 * 2 ^ (k - 2) := (pow_mul_pow_sub _ ?_).symm
      _ = 4 * 2 ^ (k - 2) := by norm_num
      
    rcases k with (_ | _ | _)
    · exfalso
      norm_num at n2
    · exfalso
      exact lt_irrefl _ n2
    · exact le_add_self
  · rw [Nat.prime_iff_prime_int] at hp
    rw [← Int.odd_coe_nat] at hodd
    exact ⟨p, Int.coe_nat_dvd.mpr hdvd, Or.inr ⟨hp, hodd⟩⟩
#align odd_prime_or_four.exists_and_dvd OddPrimeOrFour.exists_and_dvd

theorem associated_of_dvd {a p : ℤ} (ha : OddPrimeOrFour a) (hp : OddPrimeOrFour p) (h : p ∣ a) :
    Associated p a :=
  by
  obtain rfl | ⟨ap, aodd⟩ := ha <;> obtain rfl | ⟨pp, podd⟩ := hp
  · rfl
  · exfalso
    have h0 : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [h0] at h
    refine' Int.even_iff_not_odd.mp _ podd
    rw [even_iff_two_dvd]
    apply Associated.dvd _
    exact ((pp.dvd_prime_iff_associated Int.prime_two).mp (pp.dvd_of_dvd_pow h)).symm
  · exfalso
    rw [Int.odd_iff_not_even] at aodd
    refine' aodd _
    rw [even_iff_two_dvd]
    refine' dvd_trans _ h
    norm_num
  · rwa [Prime.dvd_prime_iff_associated pp ap] at h
#align associated_of_dvd associated_of_dvd

theorem dvd_or_dvd {a p x : ℤ} (ha : OddPrimeOrFour a) (hp : OddPrimeOrFour p) (hdvd : p ∣ a * x) :
    p ∣ a ∨ p ∣ x := by
  obtain rfl | ⟨pp, -⟩ := hp
  · obtain rfl | ⟨ap, aodd⟩ := ha
    · exact Or.inl dvd_rfl
    · right
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this] at hdvd⊢
      apply Int.prime_two.pow_dvd_of_dvd_mul_left _ _ hdvd
      rwa [← even_iff_two_dvd, ← Int.odd_iff_not_even]
  · exact pp.dvd_or_dvd hdvd
#align dvd_or_dvd dvd_or_dvd

theorem exists_associated_mem_of_dvd_prod'' {p : ℤ} (hp : OddPrimeOrFour p) {s : Multiset ℤ}
    (hs : ∀ r ∈ s, OddPrimeOrFour r) (hdvd : p ∣ s.prod) : ∃ q ∈ s, Associated p q :=
  by
  induction' s using Multiset.induction_on with a s ih hs
  · simp [hp.not_unit, ← isUnit_iff_dvd_one] at hdvd
  · rw [Multiset.prod_cons] at hdvd
    have := hs a (Multiset.mem_cons_self _ _)
    obtain h | h := dvd_or_dvd this hp hdvd
    · exact ⟨a, Multiset.mem_cons_self _ _, associated_of_dvd this hp h⟩
    · obtain ⟨q, hq₁, hq₂⟩ := ih (fun r hr => hs _ (Multiset.mem_cons_of_mem hr)) h
      exact ⟨q, Multiset.mem_cons_of_mem hq₁, hq₂⟩
#align exists_associated_mem_of_dvd_prod'' exists_associated_mem_of_dvd_prod''

theorem factors_unique_prod' :
    ∀ {f g : Multiset ℤ},
      (∀ x ∈ f, OddPrimeOrFour x) →
        (∀ x ∈ g, OddPrimeOrFour x) → Associated f.prod g.prod → Multiset.Rel Associated f g :=
  by
  intro f
  induction' f using Multiset.induction_on with p f ih
  · rintro g - hg h
    rw [Multiset.prod_zero] at h
    rw [Multiset.rel_zero_left]
    apply Multiset.eq_zero_of_forall_not_mem
    intro x hx
    apply (hg x hx).not_unit
    rw [isUnit_iff_dvd_one]
    exact dvd_trans (Multiset.dvd_prod hx) h.symm.dvd
  · intro g hf hg hfg
    have hp := hf p (Multiset.mem_cons_self _ _)
    have hdvd : p ∣ g.prod :=
      by
      rw [← hfg.dvd_iff_dvd_right, Multiset.prod_cons]
      exact dvd_mul_right _ _
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod'' hp hg hdvd
    rw [← Multiset.cons_erase hbg]
    apply Multiset.Rel.cons hb
    apply ih _ _ _
    · exact fun q hq => hf _ (Multiset.mem_cons_of_mem hq)
    · exact fun q (hq : q ∈ g.erase b) => hg q (Multiset.mem_of_mem_erase hq)
    · apply Associated.of_mul_left _ hb hp.ne_zero
      rwa [← Multiset.prod_cons, ← Multiset.prod_cons, Multiset.cons_erase hbg]
#align factors_unique_prod' factors_unique_prod'

/-- The odd factors. -/
noncomputable def oddFactors (x : ℤ) :=
  Multiset.filter Odd (UniqueFactorizationMonoid.normalizedFactors x)
#align odd_factors oddFactors

theorem oddFactors.zero : oddFactors 0 = 0 :=
  rfl
#align odd_factors.zero oddFactors.zero

theorem oddFactors.not_two_mem (x : ℤ) : (2 : ℤ) ∉ oddFactors x := by
  simp only [oddFactors, even_bit0, not_true, not_false_iff, Int.odd_iff_not_even, and_false_iff,
    Multiset.mem_filter]
#align odd_factors.not_two_mem oddFactors.not_two_mem

theorem oddFactors.nonneg {z a : ℤ} (ha : a ∈ oddFactors z) : 0 ≤ a :=
  by
  simp only [oddFactors, Multiset.mem_filter] at ha
  exact
    Int.nonneg_of_normalize_eq_self (UniqueFactorizationMonoid.normalize_normalized_factor a ha.1)
#align odd_factors.nonneg oddFactors.nonneg

theorem oddFactors.pow (z : ℤ) (n : ℕ) : oddFactors (z ^ n) = n • oddFactors z :=
  by
  simp only [oddFactors]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.filter_nsmul]
#align odd_factors.pow oddFactors.pow

/-- The exponent of `2` in the factorization. -/
noncomputable def evenFactorExp (x : ℤ) :=
  Multiset.count 2 (UniqueFactorizationMonoid.normalizedFactors x)
#align even_factor_exp evenFactorExp

theorem evenFactorExp.def (x : ℤ) :
    evenFactorExp x = Multiset.count 2 (UniqueFactorizationMonoid.normalizedFactors x) :=
  rfl
#align even_factor_exp.def evenFactorExp.def

theorem evenFactorExp.zero : evenFactorExp 0 = 0 :=
  rfl
#align even_factor_exp.zero evenFactorExp.zero

theorem evenFactorExp.pow (z : ℤ) (n : ℕ) : evenFactorExp (z ^ n) = n * evenFactorExp z :=
  by
  simp only [evenFactorExp]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
#align even_factor_exp.pow evenFactorExp.pow

theorem even_and_odd_factors'' (x : ℤ) :
    UniqueFactorizationMonoid.normalizedFactors x =
      (UniqueFactorizationMonoid.normalizedFactors x).filter (Eq 2) + oddFactors x :=
  by
  by_cases hx : x = 0
  ·
    rw [hx, UniqueFactorizationMonoid.normalizedFactors_zero, oddFactors.zero, Multiset.filter_zero,
      add_zero]
  simp [evenFactorExp, oddFactors]
  rw [Multiset.filter_add_filter]
  convert (add_zero
    (Multiset.filter (fun a => 2 = a ∨ Odd a) (UniqueFactorizationMonoid.normalizedFactors x))).symm
  · symm
    rw [Multiset.filter_eq_self]
    intro a ha
    have hprime : Prime a := UniqueFactorizationMonoid.prime_of_normalized_factor a ha
    have := UniqueFactorizationMonoid.normalize_normalized_factor a ha
    rw [← Int.abs_eq_normalize, ← Int.coe_natAbs] at this
    rw [← this]
    rw [Int.prime_iff_natAbs_prime] at hprime
    rcases Nat.Prime.eq_two_or_odd' hprime with (h2 | hodd)
    · simp [h2]
    · right
      rw [this]
      exact Int.natAbs_odd.1 hodd
  · rw [Multiset.filter_eq_nil]
    rintro a ha ⟨rfl, hodd⟩
    norm_num at hodd
#align even_and_odd_factors'' even_and_odd_factors''

theorem even_and_odd_factors' (x : ℤ) :
    UniqueFactorizationMonoid.normalizedFactors x =
      Multiset.replicate (evenFactorExp x) 2 + oddFactors x :=
  by
  convert even_and_odd_factors'' x
  simp [evenFactorExp, ← Multiset.filter_eq]
#align even_and_odd_factors' even_and_odd_factors'

theorem even_and_oddFactors (x : ℤ) (hx : x ≠ 0) :
    Associated x (2 ^ evenFactorExp x * (oddFactors x).prod) :=
  by
  convert(UniqueFactorizationMonoid.normalizedFactors_prod hx).symm
  simp [evenFactorExp]
  rw [Multiset.pow_count, ← Multiset.prod_add, ← even_and_odd_factors'' x]
#align even_and_odd_factors even_and_oddFactors

theorem factors_2_even {z : ℤ} (hz : z ≠ 0) : evenFactorExp (4 * z) = 2 + evenFactorExp z :=
  by
  have h₀ : (4 : ℤ) ≠ 0 := four_ne_zero
  have h₁ : (2 : Int) ^ 2 = 4 := by norm_num
  simp [evenFactorExp]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul h₀ hz, Multiset.count_add, ← h₁,
    UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
    UniqueFactorizationMonoid.normalizedFactors_irreducible Int.prime_two.irreducible,
    Int.normalize_of_nonneg zero_le_two, Multiset.count_singleton_self, mul_one]
#align factors_2_even factors_2_even

-- most useful with  (hz : even (even_factor_exp z))
/-- Odd factors or `4`. -/
noncomputable def factorsOddPrimeOrFour (z : ℤ) : Multiset ℤ :=
  Multiset.replicate (evenFactorExp z / 2) 4 + oddFactors z
#align factors_odd_prime_or_four factorsOddPrimeOrFour

theorem factorsOddPrimeOrFour.nonneg {z a : ℤ} (ha : a ∈ factorsOddPrimeOrFour z) : 0 ≤ a :=
  by
  simp only [factorsOddPrimeOrFour, Multiset.mem_add] at ha
  cases ha with
  | inl ha =>
    rw [Multiset.eq_of_mem_replicate ha]
    norm_num
  | inr ha =>
    exact oddFactors.nonneg ha
#align factors_odd_prime_or_four.nonneg factorsOddPrimeOrFour.nonneg

theorem factorsOddPrimeOrFour.prod' {a : ℤ} (ha : 0 < a) (heven : Even (evenFactorExp a)) :
    (factorsOddPrimeOrFour a).prod = a :=
  by
  apply Int.eq_of_associated_of_nonneg
  · have := UniqueFactorizationMonoid.normalizedFactors_prod ha.ne'
    apply Associated.trans _ this
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp heven
    rw [even_and_odd_factors' _, Multiset.prod_add, factorsOddPrimeOrFour, Multiset.prod_add, hm,
      Nat.mul_div_right _ zero_lt_two, Multiset.prod_replicate, Multiset.prod_replicate, pow_mul]
    exact Associated.refl _
  · apply Multiset.prod_nonneg
    apply factorsOddPrimeOrFour.nonneg
  · exact ha.le
#align factors_odd_prime_or_four.prod' factorsOddPrimeOrFour.prod'

theorem factorsOddPrimeOrFour.associated' {a : ℤ} {f : Multiset ℤ} (hf : ∀ x ∈ f, OddPrimeOrFour x)
    (ha : 0 < a) (heven : Even (evenFactorExp a)) (hassoc : Associated f.prod a) :
    Multiset.Rel Associated f (factorsOddPrimeOrFour a) :=
  by
  apply factors_unique_prod' hf
  · intro x hx
    simp only [factorsOddPrimeOrFour, Multiset.mem_add] at hx
    apply Or.imp _ _ hx
    · exact Multiset.eq_of_mem_replicate
    · simp only [oddFactors, Multiset.mem_filter]
      exact And.imp_left (UniqueFactorizationMonoid.prime_of_normalized_factor _)
  · rwa [factorsOddPrimeOrFour.prod' ha heven]
#align factors_odd_prime_or_four.associated' factorsOddPrimeOrFour.associated'

theorem factorsOddPrimeOrFour.unique' {a : ℤ} {f : Multiset ℤ} (hf : ∀ x ∈ f, OddPrimeOrFour x)
    (hf' : ∀ x ∈ f, (0 : ℤ) ≤ x) (ha : 0 < a) (heven : Even (evenFactorExp a))
    (hassoc : Associated f.prod a) : f = factorsOddPrimeOrFour a :=
  by
  rw [← Multiset.rel_eq]
  apply Multiset.Rel.mono (factorsOddPrimeOrFour.associated' hf ha heven hassoc)
  intro x hx y hy hxy
  exact Int.eq_of_associated_of_nonneg hxy (hf' x hx) (factorsOddPrimeOrFour.nonneg hy)
#align factors_odd_prime_or_four.unique' factorsOddPrimeOrFour.unique'

theorem factorsOddPrimeOrFour.pow (z : ℤ) (n : ℕ) (hz : Even (evenFactorExp z)) :
    factorsOddPrimeOrFour (z ^ n) = n • factorsOddPrimeOrFour z := by
  simp only [factorsOddPrimeOrFour, nsmul_add, Multiset.nsmul_replicate, evenFactorExp.pow,
    Nat.mul_div_assoc _ (even_iff_two_dvd.mp hz), oddFactors.pow]
#align factors_odd_prime_or_four.pow factorsOddPrimeOrFour.pow