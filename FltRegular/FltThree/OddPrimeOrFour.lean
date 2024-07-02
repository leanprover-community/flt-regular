/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Int.Basic

/-- Being equal to `4` or odd. -/
def OddPrimeOrFour (z : ℕ) : Prop :=
  z = 4 ∨ Nat.Prime z ∧ Odd z

theorem OddPrimeOrFour.ne_zero {z : ℕ} (h : OddPrimeOrFour z) : z ≠ 0 :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · norm_num
  · exact h.ne_zero

theorem OddPrimeOrFour.ne_one {z : ℕ} (h : OddPrimeOrFour z) : z ≠ 1 :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · norm_num
  · exact h.ne_one

theorem OddPrimeOrFour.one_lt {z : ℕ} (h : OddPrimeOrFour z) : 1 < z :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · norm_num
  · exact h.one_lt

theorem OddPrimeOrFour.not_unit {z : ℕ} (h : OddPrimeOrFour z) : ¬IsUnit z :=
  by
  obtain rfl | ⟨h, -⟩ := h
  · rw [isUnit_iff_dvd_one]
    norm_num
  · exact h.not_unit

theorem OddPrimeOrFour.exists_and_dvd {n : ℕ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ OddPrimeOrFour p := by
  obtain h4 | ⟨p, hpprime, hpdvd, hpodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt n2
  · exact ⟨4, h4, Or.inl rfl⟩
  · exact ⟨p, hpdvd, Or.inr ⟨hpprime, hpodd⟩⟩

theorem eq_of_dvd {a p : ℕ} (ha : OddPrimeOrFour a) (hp : OddPrimeOrFour p) (h : p ∣ a) :
    p = a :=
  by
  obtain rfl | ⟨ap, aodd⟩ := ha <;> obtain rfl | ⟨pp, podd⟩ := hp
  · rfl
  · exfalso
    have h0 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h0] at h
    refine' Nat.even_iff_not_odd.mp _ podd
    rw [even_iff_two_dvd]
    exact pp.dvd_symm Nat.prime_two (pp.dvd_of_dvd_pow h)
  · exfalso
    rw [Nat.odd_iff_not_even] at aodd
    refine' aodd _
    rw [even_iff_two_dvd]
    refine' dvd_trans _ h
    norm_num
  · rwa [Nat.prime_dvd_prime_iff_eq pp ap] at h

theorem dvd_or_dvd {a p x : ℕ} (ha : OddPrimeOrFour a) (hp : OddPrimeOrFour p) (hdvd : p ∣ a * x) :
    p ∣ a ∨ p ∣ x := by
  obtain rfl | ⟨pp, -⟩ := hp
  · obtain rfl | ⟨ap, aodd⟩ := ha
    · exact Or.inl dvd_rfl
    · right
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this] at hdvd⊢
      apply Nat.prime_two.prime.pow_dvd_of_dvd_mul_left _ _ hdvd
      rwa [← even_iff_two_dvd, ← Nat.odd_iff_not_even]
  · exact pp.dvd_mul.mp hdvd

theorem mem_of_dvd_prod {p : ℕ} (hp : OddPrimeOrFour p) {s : Multiset ℕ}
    (hs : ∀ r ∈ s, OddPrimeOrFour r) (hdvd : p ∣ s.prod) : p ∈ s :=
  by
  induction' s using Multiset.induction_on with a s ih hs
  · simp [hp.ne_one] at hdvd
  · rw [Multiset.prod_cons] at hdvd
    have := hs a (Multiset.mem_cons_self _ _)
    obtain h | h := dvd_or_dvd this hp hdvd
    · rw [eq_of_dvd this hp h]
      exact Multiset.mem_cons_self _ _
    · have := ih (fun r hr => hs _ (Multiset.mem_cons_of_mem hr)) h
      exact Multiset.mem_cons_of_mem this

theorem factors_unique_prod' :
    ∀ {f g : Multiset ℕ},
      (∀ x ∈ f, OddPrimeOrFour x) →
        (∀ x ∈ g, OddPrimeOrFour x) →
          f.prod = g.prod → f = g :=
  by
  intro f
  induction' f using Multiset.induction_on with p f ih
  · rintro g - hg h
    rw [Multiset.prod_zero] at h
    symm
    apply Multiset.eq_zero_of_forall_not_mem
    intro x hx
    apply (hg x hx).not_unit
    rw [isUnit_iff_dvd_one]
    exact dvd_trans (Multiset.dvd_prod hx) h.symm.dvd
  · intro g hf hg hfg
    have hp := hf p (Multiset.mem_cons_self _ _)
    have hdvd : p ∣ g.prod :=
      by
      rw [← hfg, Multiset.prod_cons]
      exact dvd_mul_right _ _
    have hbg := mem_of_dvd_prod hp hg hdvd
    rw [← Multiset.cons_erase hbg]
    congr
    apply ih _ _ _
    · exact fun q hq => hf _ (Multiset.mem_cons_of_mem hq)
    · exact fun q hq => hg q (Multiset.mem_of_mem_erase hq)
    · apply mul_left_cancel₀ hp.ne_zero
      rwa [Multiset.prod_erase hbg, ← Multiset.prod_cons]

/-- The odd factors. -/
noncomputable def oddFactors (x : ℕ) :=
  Multiset.filter Odd (UniqueFactorizationMonoid.normalizedFactors x)

theorem oddFactors.zero : oddFactors 0 = 0 := by
  simp [oddFactors]

theorem oddFactors.pow (z : ℕ) (n : ℕ) : oddFactors (z ^ n) = n • oddFactors z :=
  by
  simp only [oddFactors]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.filter_nsmul]

/-- The exponent of `2` in the factorization. -/
noncomputable def evenFactorExp (x : ℕ) :=
  Multiset.count 2 (UniqueFactorizationMonoid.normalizedFactors x)

theorem evenFactorExp.def (x : ℕ) :
    evenFactorExp x = Multiset.count 2 (UniqueFactorizationMonoid.normalizedFactors x) :=
  rfl

theorem evenFactorExp.zero : evenFactorExp 0 = 0 := by
  simp [evenFactorExp]

theorem evenFactorExp.pow (z : ℕ) (n : ℕ) : evenFactorExp (z ^ n) = n * evenFactorExp z :=
  by
  simp only [evenFactorExp]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]

theorem even_and_odd_factors'' (x : ℕ) :
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
    rw [eq_comm]
    have hprime : Prime a := UniqueFactorizationMonoid.prime_of_normalized_factor a ha
    exact hprime.nat_prime.eq_two_or_odd'
  · rw [Multiset.filter_eq_nil]
    rintro a ha ⟨rfl, hodd⟩
    norm_num at hodd

theorem even_and_odd_factors' (x : ℕ) :
    UniqueFactorizationMonoid.normalizedFactors x =
      Multiset.replicate (evenFactorExp x) 2 + oddFactors x :=
  by
  convert even_and_odd_factors'' x
  simp [evenFactorExp, ← Multiset.filter_eq]

theorem even_and_oddFactors (x : ℕ) (hx : x ≠ 0) :
    Associated x (2 ^ evenFactorExp x * (oddFactors x).prod) :=
  by
  convert(UniqueFactorizationMonoid.normalizedFactors_prod hx).symm
  simp [evenFactorExp]
  rw [Multiset.pow_count, ← Multiset.prod_add, ← even_and_odd_factors'' x]

theorem factors_2_even {z : ℕ} (hz : z ≠ 0) : evenFactorExp (4 * z) = 2 + evenFactorExp z :=
  by
  have h₀ : (4 : ℕ) ≠ 0 := four_ne_zero
  have h₁ : (2 : ℕ) ^ 2 = 4 := by norm_num
  simp [evenFactorExp]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul h₀ hz, Multiset.count_add, ← h₁,
    UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
    UniqueFactorizationMonoid.normalizedFactors_irreducible Nat.prime_two,
    normalize_eq, Multiset.count_singleton_self, mul_one]

-- most useful with  (hz : even (even_factor_exp z))
/-- Odd factors or `4`. -/
noncomputable def factorsOddPrimeOrFour (z : ℕ) : Multiset ℕ :=
  Multiset.replicate (evenFactorExp z / 2) 4 + oddFactors z

theorem factorsOddPrimeOrFour.prod' {a : ℕ} (ha : 0 < a) (heven : Even (evenFactorExp a)) :
    (factorsOddPrimeOrFour a).prod = a :=
  by
  have h₁ : (2 : ℕ) ^ 2 = 4 := by norm_num
  have := UniqueFactorizationMonoid.normalizedFactors_prod ha.ne'
  rw [associated_eq_eq] at this
  conv_rhs => rw [←this]
  obtain ⟨m, hm⟩ := even_iff_two_dvd.mp heven
  rw [even_and_odd_factors' _, Multiset.prod_add, factorsOddPrimeOrFour, Multiset.prod_add, hm,
    Nat.mul_div_right _ zero_lt_two, Multiset.prod_replicate, Multiset.prod_replicate, pow_mul, h₁]

theorem factorsOddPrimeOrFour.unique' {f : Multiset ℕ} (hf : ∀ x ∈ f, OddPrimeOrFour x)
    (ha : 0 < f.prod) (heven : Even (evenFactorExp f.prod)) :
    factorsOddPrimeOrFour f.prod = f:=
  by
  refine factors_unique_prod' ?_ hf (factorsOddPrimeOrFour.prod' ha heven)
  intro x hx
  simp only [factorsOddPrimeOrFour, Multiset.mem_add] at hx
  apply Or.imp _ _ hx
  · exact Multiset.eq_of_mem_replicate
  · simp only [oddFactors, Multiset.mem_filter]
    exact And.imp_left <| Prime.nat_prime ∘ (UniqueFactorizationMonoid.prime_of_normalized_factor _)

theorem factorsOddPrimeOrFour.pow (z : ℕ) (n : ℕ) (hz : Even (evenFactorExp z)) :
    factorsOddPrimeOrFour (z ^ n) = n • factorsOddPrimeOrFour z := by
  simp only [factorsOddPrimeOrFour, nsmul_add, Multiset.nsmul_replicate, evenFactorExp.pow,
    Nat.mul_div_assoc _ (even_iff_two_dvd.mp hz), oddFactors.pow]
