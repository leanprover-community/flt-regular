/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FltRegular.FltThree.Primes
import FltRegular.FltThree.Spts
import FltRegular.FltThree.OddPrimeOrFour

theorem Zsqrtd.associated_norm_of_associated {d : ℤ} {f g : ℤ√d} (h : Associated f g) :
    Associated f.norm g.norm := by
  obtain ⟨u, rfl⟩ := h
  have := (Zsqrtd.isUnit_iff_norm_isUnit u).mp u.isUnit
  rw [Zsqrtd.norm_mul]
  exact associated_mul_unit_right (Zsqrtd.norm f) _ this

theorem OddPrimeOrFour.im_ne_zero {p : ℤ√(-3)} (h : OddPrimeOrFour p.norm.natAbs)
    (hcoprime : IsCoprime p.re p.im) : p.im ≠ 0 :=
  by
  intro H
  rw [Zsqrtd.norm_def, H, MulZeroClass.mul_zero, sub_zero, ← pow_two] at h
  obtain h | ⟨hp, -⟩ := h
  · rw [H, isCoprime_zero_right, Int.isUnit_iff_abs_eq] at hcoprime
    rw [← sq_abs, hcoprime] at h
    norm_num at h
  · rw [Int.natAbs_pow] at hp
    exact hp.not_prime_pow le_rfl

theorem Zsqrt3.isUnit_iff {z : ℤ√(-3)} : IsUnit z ↔ abs z.re = 1 ∧ z.im = 0 :=
  by
  rw [← Zsqrtd.norm_eq_one_iff, ← Int.natCast_inj, Int.ofNat_one,
    Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) z)]
  refine' ⟨Spts.eq_one, fun h => _⟩
  rw [Zsqrtd.norm_def, h.2, MulZeroClass.mul_zero, sub_zero, ← sq, ← sq_abs, h.1, one_pow]

theorem Zsqrt3.coe_of_isUnit {z : ℤ√(-3)} (h : IsUnit z) : ∃ u : Units ℤ, z = u :=
  by
  obtain ⟨u, hu⟩ := Zsqrt3.isUnit_iff.mp h
  obtain ⟨v, hv⟩ : IsUnit z.re := by rwa [Int.isUnit_iff_abs_eq]
  use v
  rw [Zsqrtd.ext_iff, hu, ← hv]
  simp only [Zsqrtd.intCast_re, and_true_iff, eq_self_iff_true, Zsqrtd.intCast_im]

theorem Zsqrt3.coe_of_isUnit' {z : ℤ√(-3)} (h : IsUnit z) : ∃ u : ℤ, z = u ∧ abs u = 1 :=
  by
  obtain ⟨u, hu⟩ := Zsqrt3.coe_of_isUnit h
  refine' ⟨u, _, _⟩
  · rw [hu]
  · exact Int.isUnit_iff_abs_eq.mp u.isUnit

theorem Zsqrt3.norm_natAbs (a : ℤ√(-3)) : a.norm.natAbs = a.norm := by
  rw [Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) a)]

theorem OddPrimeOrFour.factors (a : ℤ√(-3)) (x : ℤ) (hcoprime : IsCoprime a.re a.im)
    (hx : OddPrimeOrFour x.natAbs) (hfactor : x ∣ a.norm) :
    ∃ c : ℤ√(-3), |x| = c.norm ∧ 0 ≤ c.re ∧ c.im ≠ 0 :=
  by
  obtain hx | ⟨hprime, hodd⟩ := hx
  · refine' ⟨⟨1, 1⟩, _, zero_le_one, one_ne_zero⟩
    simp only [Zsqrtd.norm_def, mul_one, sub_neg_eq_add, Int.abs_eq_natAbs, hx]
    norm_num
  · rw [Int.natAbs_odd] at hodd
    obtain ⟨c, hc⟩ := _root_.factors a x hcoprime hodd hfactor
    rw [hc]
    apply Zsqrtd.exists c
    intro H
    rw [Zsqrtd.norm_def, H, MulZeroClass.mul_zero, sub_zero, ← pow_two, eq_comm, Int.abs_eq_natAbs]
      at hc
    rw [Nat.prime_iff_prime_int, ← hc] at hprime
    exact not_prime_pow one_lt_two.ne' hprime

theorem step1a {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) (heven : Even a.norm) :
    Odd a.re ∧ Odd a.im :=
  by
  rw [Int.odd_iff_not_even, Int.odd_iff_not_even]
  have : Even a.re ↔ Even a.im := by
    have : ¬ Even (3 : ℤ) := by decide
    simpa [this, Zsqrtd.norm_def, parity_simps] using heven
  apply (iff_iff_and_or_not_and_not.mp this).resolve_left
  rw [even_iff_two_dvd, even_iff_two_dvd]
  rintro ⟨hre, him⟩
  have := hcoprime.isUnit_of_dvd' hre him
  rw [isUnit_iff_dvd_one] at this
  norm_num at this

theorem step1 {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) (heven : Even a.norm) :
    ∃ u : ℤ√(-3), a = ⟨1, 1⟩ * u ∨ a = ⟨1, -1⟩ * u :=
  by
  obtain ⟨ha, hb⟩ := step1a hcoprime heven
  obtain hdvd | hdvd := Int.four_dvd_add_or_sub_of_odd ha hb
  · obtain ⟨v, hv⟩ := hdvd
    rw [← eq_sub_iff_add_eq] at hv
    use ⟨v - a.im, v⟩
    right
    rw [Zsqrtd.ext_iff, hv, Zsqrtd.mul_re, Zsqrtd.mul_im]
    dsimp only
    constructor <;> ring
  · obtain ⟨v, hv⟩ := hdvd
    rw [sub_eq_iff_eq_add] at hv
    use ⟨a.im + v, -v⟩
    left
    rw [Zsqrtd.ext_iff, hv, Zsqrtd.mul_re, Zsqrtd.mul_im]
    dsimp only
    constructor <;> ring

theorem step1' {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) (heven : Even a.norm) :
    ∃ u : ℤ√(-3), IsCoprime u.re u.im ∧ a.norm = 4 * u.norm :=
  by
  obtain ⟨u', hu'⟩ := step1 hcoprime heven
  refine' ⟨u', _, _⟩
  · apply Zsqrtd.coprime_of_dvd_coprime hcoprime
    obtain rfl | rfl := hu' <;> apply dvd_mul_left
  · cases' hu' with hu' hu' <;>
      · rw [hu', Zsqrtd.norm_mul]
        congr

theorem step1'' {a p : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) (hp : p.norm = 4) (hq : p.im ≠ 0)
    (heven : Even a.norm) :
    ∃ u : ℤ√(-3), IsCoprime u.re u.im ∧ (a = p * u ∨ a = star p * u) ∧ a.norm = 4 * u.norm :=
  by
  obtain ⟨u, h2⟩ := step1 hcoprime heven
  set q : ℤ√(-3) := ⟨1, 1⟩
  replace h2 : a = q * u ∨ a = star q * u := h2
  obtain ⟨hp', hq'⟩ := Spts.four hp hq
  refine' ⟨p.re * u, _, _, _⟩
  · rw [← Int.isUnit_iff_abs_eq] at hp'
    rw [Zsqrtd.smul_re, Zsqrtd.smul_im, isCoprime_mul_unit_left hp']
    apply Zsqrtd.coprime_of_dvd_coprime hcoprime
    obtain rfl | rfl := h2 <;> apply dvd_mul_left
  · rw [abs_eq <| zero_le_one' ℤ] at hp' hq'
    cases hp' with
    | inl hp' =>
      have h4 : p = q ∨ p = star q := by
        apply Or.imp _ _ hq' <;>
          · intro h5
            simp [Zsqrtd.ext_iff, hp', h5]
      simp only [hp', one_mul, Int.cast_one]
      cases h4 <;> cases h2 <;> simp [*, or_comm]
    | inr hp' =>
      have h4 : p = -q ∨ p = -star q := by
        apply Or.imp _ _ hq'.symm
        · intro h5
          simp [Zsqrtd.ext_iff, hp', h5]
        · intro h5
          simp [Zsqrtd.ext_iff, hp', h5]
      simp only [hp', one_mul, Zsqrtd.norm_neg, Int.cast_one, Int.cast_neg, neg_one_mul]
      cases h4 <;> cases h2 <;> simp [*]
  · rw [Zsqrtd.norm_mul, Zsqrtd.norm_intCast, ← sq, ← sq_abs, hp', one_pow, one_mul]
    cases' h2 with h2 h2 <;>
      · rw [h2, Zsqrtd.norm_mul]
        congr

theorem step2 {a p : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) (hdvd : p.norm ∣ a.norm)
    (hpprime : Prime p.norm) :
    ∃ u : ℤ√(-3), IsCoprime u.re u.im ∧ (a = p * u ∨ a = star p * u) ∧
    a.norm = p.norm * u.norm := by
  obtain ⟨u', h, h'⟩ := Spts.mul_of_dvd'' hdvd hpprime
  refine' ⟨u', _, h, h'⟩
  apply Zsqrtd.coprime_of_dvd_coprime hcoprime
  obtain rfl | rfl := h <;> apply dvd_mul_left

theorem step1_2 {a p : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) (hdvd : p.norm ∣ a.norm)
    (hp : OddPrimeOrFour p.norm.natAbs) (hq : p.im ≠ 0) :
    ∃ u : ℤ√(-3), IsCoprime u.re u.im ∧ (a = p * u ∨ a = star p * u) ∧
    a.norm = p.norm * u.norm := by
  obtain hp | ⟨hpprime, -⟩ := hp
  · replace hp : p.norm = 4 := by
      rw [← Zsqrt3.norm_natAbs]
      norm_cast
    rw [hp] at hdvd⊢
    have heven : Even a.norm :=
      by
      apply even_iff_two_dvd.mpr (dvd_trans _ hdvd)
      norm_num
    exact step1'' hcoprime hp hq heven
  · rw [← Int.prime_iff_natAbs_prime] at hpprime
    apply step2 hcoprime hdvd hpprime

theorem OddPrimeOrFour.factors' {a : ℤ√(-3)} (h2 : a.norm ≠ 1) (hcoprime : IsCoprime a.re a.im) :
    ∃ u q : ℤ√(-3),
      0 ≤ q.re ∧
        q.im ≠ 0 ∧ OddPrimeOrFour q.norm.natAbs ∧ a = q * u ∧ IsCoprime u.re u.im ∧ u.norm < a.norm :=
  by
  have h2 : 2 < a.norm.natAbs := by
    zify
    rw [abs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) a)]
    apply lt_of_le_of_ne _ (Spts.not_two _).symm
    rw [← one_mul (2 : ℤ), mul_two, Int.add_one_le_iff]
    apply lt_of_le_of_ne _ h2.symm
    rw [← Int.sub_one_lt_iff, sub_self]
    exact Spts.pos_of_coprime' hcoprime
  obtain ⟨p, hpdvd, hp⟩ := OddPrimeOrFour.exists_and_dvd h2
  rw [← Int.ofNat_dvd_left] at hpdvd
  obtain ⟨q', hcd, hc, hd⟩ := OddPrimeOrFour.factors a p hcoprime hp hpdvd
  rw [Nat.abs_cast, ← Zsqrt3.norm_natAbs, Nat.cast_inj] at hcd
  rw [hcd] at hpdvd hp
  rw [Int.natAbs_dvd] at hpdvd
  obtain ⟨u, huvcoprime, huv, huvdvd⟩ := step1_2 hcoprime hpdvd hp hd
  use u
  cases' huv with huv huv <;> [(use q'); (use star q')] <;>
    simp only [IsCoprime, Zsqrtd.star_re, Zsqrtd.star_im, Ne.def, neg_eq_zero, Zsqrtd.norm_conj] <;>
    use hc, hd, hp, huv, huvcoprime <;>
    · rw [huvdvd, lt_mul_iff_one_lt_left (Spts.pos_of_coprime' huvcoprime), ← Zsqrt3.norm_natAbs,
        Nat.one_lt_cast]
      exact hp.one_lt

theorem step3 {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) :
    ∃ f : Multiset (ℤ√(-3)),
      (a = f.prod ∨ a = -f.prod) ∧
        ∀ pq : ℤ√(-3), pq ∈ f → 0 ≤ pq.re ∧ pq.im ≠ 0 ∧ OddPrimeOrFour pq.norm.natAbs :=
  by
  suffices
    ∀ n : ℕ,
      a.norm.natAbs = n →
        ∃ f : Multiset (ℤ√(-3)),
          (a = f.prod ∨ a = -f.prod) ∧
            ∀ pq : ℤ√(-3), pq ∈ f → 0 ≤ pq.re ∧ pq.im ≠ 0 ∧ OddPrimeOrFour pq.norm.natAbs
    by exact this a.norm.natAbs rfl
  intro n hn
  induction' n using Nat.strong_induction_on with n ih generalizing a
  cases' eq_or_ne a.norm 1 with h h
  · use 0
    constructor
    · simp only [Multiset.prod_zero, Spts.eq_one' h]
    · intro pq hpq
      exact absurd hpq (Multiset.not_mem_zero _)
  · obtain ⟨U, q, hc, hd, hp, huv, huvcoprime, descent⟩ := OddPrimeOrFour.factors' h hcoprime
    replace descent :=
      Int.natAbs_lt_natAbs_of_nonneg_of_lt (Zsqrtd.norm_nonneg (by norm_num) _) descent
    rw [hn] at descent
    obtain ⟨g, hgprod, hgfactors⟩ := ih U.norm.natAbs descent huvcoprime rfl
    refine' ⟨q ::ₘ g, _, _⟩
    · simp only [huv, Multiset.prod_cons, ← mul_neg]
      exact Or.imp (congr_arg _) (congr_arg _) hgprod
    · rintro pq hpq
      rw [Multiset.mem_cons] at hpq
      obtain rfl | ind := hpq
      · exact ⟨hc, hd, hp⟩
      · exact hgfactors pq ind

theorem step4_3 {p p' : ℤ√(-3)} (hcoprime : IsCoprime p.re p.im) (hcoprime' : IsCoprime p'.re p'.im)
    (h : OddPrimeOrFour p.norm.natAbs) (heq : p.norm = p'.norm) :
    abs p.re = abs p'.re ∧ abs p.im = abs p'.im :=
  by
  have hdvd : p'.norm ∣ p.norm := by rw [heq]
  have him : p'.im ≠ 0 := by
    apply OddPrimeOrFour.im_ne_zero _ hcoprime'
    rwa [← heq]
  obtain ⟨u, -, H | H, h1⟩ := step1_2 hcoprime hdvd (by rwa [← heq]) him <;>
    · rw [heq] at h1
      have := Int.eq_one_of_mul_eq_self_right (Spts.ne_zero_of_coprime' _ hcoprime') h1.symm
      obtain ⟨ha, hb⟩ := Spts.eq_one this
      simp only [hb, Zsqrtd.ext_iff, Zsqrtd.mul_re, Zsqrtd.mul_im, add_zero, zero_add,
        MulZeroClass.mul_zero] at H
      rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one]
      try rw [zsqrtd.conj_re, zsqrtd.conj_im, abs_neg]
      simp

theorem prod_map_norm {d : ℤ} {s : Multiset (ℤ√d)} :
    (s.map Zsqrtd.norm).prod = Zsqrtd.norm s.prod :=
  Multiset.prod_hom s (Zsqrtd.normMonoidHom : ℤ√d →* ℤ)

theorem prod_map_natAbs {s : Multiset ℤ} :
    (s.map Int.natAbs).prod = Int.natAbs s.prod :=
  Multiset.prod_hom s <|
    ({  toFun := Int.natAbs
        map_one' := rfl
        map_mul' := fun x y => Int.natAbs_mul x y } : ℤ →* ℕ)

theorem factors_unique_prod :
    ∀ {f g : Multiset (ℤ√(-3))},
      (∀ x ∈ f, OddPrimeOrFour (Zsqrtd.norm x).natAbs) →
        (∀ x ∈ g, OddPrimeOrFour (Zsqrtd.norm x).natAbs) →
          Associated f.prod.norm g.prod.norm →
            (f.map (Int.natAbs ∘ Zsqrtd.norm)) = (g.map (Int.natAbs ∘ Zsqrtd.norm)) :=
  by
  intro f g hf hg hassoc
  refine factors_unique_prod' ?_ ?_ ?_
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hf y hy
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hg y hy
  · simp_rw [← Multiset.map_map, prod_map_natAbs, prod_map_norm, ← Int.associated_iff_natAbs]
    exact hassoc

/-- The multiset of factors. -/
noncomputable def factorization' {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) :
    Multiset (ℤ√(-3)) :=
  Classical.choose (step3 hcoprime)

theorem factorization'_prop {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) :
    (a = (factorization' hcoprime).prod ∨ a = -(factorization' hcoprime).prod) ∧
      ∀ pq : ℤ√(-3),
        pq ∈ factorization' hcoprime → 0 ≤ pq.re ∧ pq.im ≠ 0 ∧ OddPrimeOrFour pq.norm.natAbs :=
  Classical.choose_spec (step3 hcoprime)

theorem factorization'.coprime_of_mem {a b : ℤ√(-3)} (h : IsCoprime a.re a.im)
    (hmem : b ∈ factorization' h) : IsCoprime b.re b.im :=
  by
  obtain ⟨h1, -⟩ := factorization'_prop h
  set f := factorization' h
  apply Zsqrtd.coprime_of_dvd_coprime h
  apply (Multiset.dvd_prod hmem).trans
  cases' h1 with h1 h1 <;> rw [h1]
  simp only [dvd_neg]
  rfl

theorem no_conj (s : Multiset (ℤ√(-3))) {p : ℤ√(-3)} (hp : ¬IsUnit p)
    (hcoprime : IsCoprime s.prod.re s.prod.im) : ¬(p ∈ s ∧ star p ∈ s) :=
  by
  contrapose! hp
  obtain ⟨h1, h2⟩ := hp
  by_cases him : p.im = 0
  · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem h1
    rw [Multiset.prod_cons] at hcoprime
    simp only [him, add_zero, MulZeroClass.zero_mul, Zsqrtd.mul_im, Zsqrtd.mul_re,
      MulZeroClass.mul_zero] at hcoprime
    rw [Zsqrt3.isUnit_iff]
    simp only [him, and_true_iff, eq_self_iff_true]
    rw [← Int.isUnit_iff_abs_eq]
    apply IsCoprime.isUnit_of_dvd' hcoprime <;> apply dvd_mul_right
  · have : star p ≠ p := by
      rw [Ne.def, Zsqrtd.ext_iff]
      rintro ⟨-, H⟩
      apply him
      apply eq_zero_of_neg_eq
      simpa using H
    obtain ⟨t1, rfl⟩ := Multiset.exists_cons_of_mem h1
    have : star p ∈ t1 := by
      rw [Multiset.mem_cons] at h2
      exact h2.resolve_left this
    obtain ⟨t2, rfl⟩ := Multiset.exists_cons_of_mem this
    rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, ← Zsqrtd.norm_eq_mul_conj] at hcoprime
    rw [Zsqrtd.isUnit_iff_norm_isUnit]
    apply IsCoprime.isUnit_of_dvd' hcoprime <;>
      simp only [add_zero, Zsqrtd.intCast_re, MulZeroClass.zero_mul, dvd_mul_right, Zsqrtd.mul_re,
        MulZeroClass.mul_zero, Zsqrtd.mul_im, Zsqrtd.intCast_im]

/-- Associated elements in `ℤ√-3`. -/
def Associated' (x y : ℤ√(-3)) : Prop :=
  Associated x y ∨ Associated x (star y)

@[refl]
theorem Associated'.refl (x : ℤ√(-3)) : Associated' x x :=
  Or.inl (by rfl)

theorem Associated'.norm_eq {x y : ℤ√(-3)} (h : Associated' x y) : x.norm = y.norm := by
  cases' h with h h <;> simp only [Zsqrtd.norm_eq_of_associated (by norm_num) h, Zsqrtd.norm_conj]

theorem associated'_of_abs_eq {x y : ℤ√(-3)} (hre : abs x.re = abs y.re)
    (him : abs x.im = abs y.im) : Associated' x y :=
  by
  rw [abs_eq_abs] at hre him
  cases' hre with h1 h1 <;> cases' him with h2 h2 <;>
    [
      (left; use 1);
      (right; use 1);
      (right; use -1);
      (left; use -1)
    ] <;>
    simp [Zsqrtd.ext_iff, h1, h2]

theorem associated'_of_associated_norm {x y : ℤ√(-3)}
    (h : Associated (Zsqrtd.norm x) (Zsqrtd.norm y)) (hx : IsCoprime x.re x.im)
    (hy : IsCoprime y.re y.im) (h' : OddPrimeOrFour x.norm.natAbs) : Associated' x y :=
  by
  have heq : x.norm = y.norm :=
    haveI hd : (-3 : ℤ) ≤ 0 := by norm_num
    Int.eq_of_associated_of_nonneg h (Zsqrtd.norm_nonneg hd _) (Zsqrtd.norm_nonneg hd _)
  obtain ⟨hre, him⟩ := step4_3 hx hy h' heq
  exact associated'_of_abs_eq hre him

theorem factorization'.associated'_of_norm_associated {a b c : ℤ√(-3)} (h : IsCoprime a.re a.im)
    (hbmem : b ∈ factorization' h) (hcmem : c ∈ factorization' h)
    (hnorm : Associated b.norm c.norm) : Associated' b c := by
  apply associated'_of_associated_norm
  · exact hnorm
  · exact factorization'.coprime_of_mem h hbmem
  · exact factorization'.coprime_of_mem h hcmem
  · exact ((factorization'_prop h).2 b hbmem).2.2

theorem factors_unique {f g : Multiset (ℤ√(-3))} (hf : ∀ x ∈ f, OddPrimeOrFour (Zsqrtd.norm x).natAbs)
    (hf' : ∀ x ∈ f, IsCoprime (Zsqrtd.re x) (Zsqrtd.im x))
    (hg : ∀ x ∈ g, OddPrimeOrFour (Zsqrtd.norm x).natAbs)
    (hg' : ∀ x ∈ g, IsCoprime (Zsqrtd.re x) (Zsqrtd.im x)) (h : Associated f.prod g.prod) :
    Multiset.Rel Associated' f g :=
  by
  have p :
    ∀ (x : ℤ√(-3)) (_ : x ∈ f) (y : ℤ√(-3)) (_ : y ∈ g),
      (Int.natAbs ∘ Zsqrtd.norm) x = (Int.natAbs ∘ Zsqrtd.norm) y → Associated' x y :=
    by
    intro x hx y hy hxy
    rw [Function.comp_apply, Function.comp_apply, ← Int.associated_iff_natAbs] at hxy
    apply associated'_of_associated_norm hxy
    · exact hf' x hx
    · exact hg' y hy
    · exact hf x hx
  refine' Multiset.Rel.mono _ p
  rw [← Multiset.rel_map, factors_unique_prod hf hg <| Zsqrtd.associated_norm_of_associated h,
    Multiset.rel_eq]

theorem factors_2_even' {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) :
    Even (evenFactorExp a.norm.natAbs) :=
  by
  induction' hn : a.norm.natAbs using Nat.strong_induction_on with n ih generalizing a
  by_cases hparity : Even a.norm.natAbs
  · obtain ⟨u, huvcoprime, huvprod⟩ := step1' hcoprime (Int.natAbs_even.mp hparity)
    have huv := Spts.ne_zero_of_coprime' _ huvcoprime
    have h₄ : Int.natAbs 4 = 4 := by norm_num
    rw [← hn, huvprod, Int.natAbs_mul, h₄, factors_2_even (by simpa using huv), Nat.even_add]
    apply iff_of_true even_two
    apply ih _ _ huvcoprime rfl
    rw [← hn, huvprod, Int.natAbs_mul, lt_mul_iff_one_lt_left (Int.natAbs_pos.mpr huv)]
    norm_num
  · convert even_zero (α := ℕ)
    simp only [evenFactorExp, Multiset.count_eq_zero, hn]
    contrapose! hparity with hfactor
    rw [hn, even_iff_two_dvd]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor

theorem factorsOddPrimeOrFour.unique {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) {f : Multiset ℕ}
    (hf : ∀ x ∈ f, OddPrimeOrFour x) (hassoc : f.prod = a.norm.natAbs) :
    factorsOddPrimeOrFour a.norm.natAbs = f := by
  rw [← hassoc]
  refine factorsOddPrimeOrFour.unique' hf ?_ ?_
  · rw [hassoc, Int.natAbs_pos]
    exact Spts.ne_zero_of_coprime' _ hcoprime
  · rw [hassoc]
    exact factors_2_even' hcoprime

theorem eq_or_eq_conj_of_associated_of_re_zero {x A : ℤ√(-3)} (hx : x.re = 0) (h : Associated x A) :
    x = A ∨ x = star A := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv1, hv2⟩ := Zsqrt3.coe_of_isUnit' u.isUnit
  have hA : A.re = 0 := by
    simp only [← hu, hv1, hx, add_zero, MulZeroClass.zero_mul, Zsqrtd.mul_re, MulZeroClass.mul_zero,
      Zsqrtd.intCast_im]
  rw [abs_eq <| zero_le_one' ℤ] at hv2
  cases' hv2 with hv2 hv2
  · left
    simpa only [hv1, hv2, mul_one, Int.cast_one] using hu
  · right
    simp only [hv1, hv2, mul_one, Int.cast_one, mul_neg, Int.cast_neg] at hu
    simp [← hu, hx, Zsqrtd.ext_iff]

theorem eq_or_eq_conj_iff_associated'_of_nonneg {x A : ℤ√(-3)} (hx : 0 ≤ x.re) (hA : 0 ≤ A.re) :
    Associated' x A ↔ x = A ∨ x = star A := by
  constructor
  · rintro (⟨u, hu⟩ | ⟨u, hu⟩) <;> obtain ⟨v, hv1, hv2⟩ := Zsqrt3.coe_of_isUnit' u.isUnit
    -- associated x A
    · by_cases hxre : x.re = 0
      · apply eq_or_eq_conj_of_associated_of_re_zero hxre ⟨u, hu⟩
      · rw [hv1] at hu
        rw [abs_eq <| zero_le_one' ℤ] at hv2
        cases' hv2 with habsv habsv
        · left
          rw [← hu, habsv, Int.cast_one, mul_one]
        · exfalso
          simp only [habsv, mul_one, Int.cast_one, mul_neg, Int.cast_neg] at hu
          apply lt_irrefl (0 : ℤ)
          calc
            0 ≤ A.re := hA
            _ = -x.re := ?_
            _ < 0 := ?_

          · simp only [← hu, Zsqrtd.neg_re]
          · simp only [neg_neg_iff_pos]
            exact lt_of_le_of_ne hx (Ne.symm hxre)
    -- associated x A.conj
    · by_cases hxre : x.re = 0
      · convert(eq_or_eq_conj_of_associated_of_re_zero hxre ⟨u, hu⟩).symm
        rw [star_star]
      · rw [hv1] at hu
        rw [abs_eq <| zero_le_one' ℤ] at hv2
        cases' hv2 with habsv habsv
        · right
          rw [← hu, habsv, Int.cast_one, mul_one]
        · exfalso
          simp only [habsv, mul_one, Int.cast_one, mul_neg, Int.cast_neg] at hu
          apply lt_irrefl (0 : ℤ)
          calc
            0 ≤ A.re := hA
            _ = -x.re := ?_
            _ < 0 := ?_

          · rw [← star_star A, ← hu]
            simp only [Zsqrtd.neg_re, Zsqrtd.star_re]
          · simp only [neg_neg_iff_pos]
            apply lt_of_le_of_ne hx (Ne.symm hxre)
  · rintro (rfl | rfl)
    · rfl
    · right
      rfl

theorem step5'
    -- lemma page 54
    (a : ℤ√(-3))
    (r : ℕ) (hcoprime : IsCoprime a.re a.im) (hcube : r ^ 3 = a.norm.natAbs) :
    ∃ g : Multiset (ℤ√(-3)), factorization' hcoprime = 3 • g := by
  classical
    obtain ⟨h1, h2⟩ := factorization'_prop hcoprime
    set f := factorization' hcoprime with hf
    apply Multiset.exists_smul_of_dvd_count
    intro x hx
    convert dvd_mul_right 3 (Multiset.count x.norm.natAbs (factorsOddPrimeOrFour r))
    have : Even (evenFactorExp r) :=
      by
      suffices Even (3 * evenFactorExp r)
        by
        rw [Nat.even_mul] at this
        apply this.resolve_left
        norm_num; decide
      rw [← evenFactorExp.pow r 3, hcube]
      exact factors_2_even' hcoprime
    calc
      Multiset.count x f = Multiset.card (Multiset.filter (x = ·) f) := by
        rw [Multiset.count, Multiset.countP_eq_card_filter]
      _ = Multiset.card (Multiset.filter (fun a : ℤ√(-3) => x.norm.natAbs = a.norm.natAbs) f) :=
        (congr_arg _ (Multiset.filter_congr fun A HA => ?_))
      _ = Multiset.countP (x.norm.natAbs = ·) (Multiset.map (Int.natAbs ∘ Zsqrtd.norm) f) :=
        (Multiset.countP_map _ f (x.norm.natAbs = ·)).symm
      _ = Multiset.countP (x.norm.natAbs = ·) ((factorsOddPrimeOrFour a.norm.natAbs)) := ?_
      _ = Multiset.count x.norm.natAbs ((factorsOddPrimeOrFour a.norm.natAbs)) := by rw [Multiset.count]
      _ = Multiset.count x.norm.natAbs ((factorsOddPrimeOrFour (r ^ 3))) := by rw [hcube]
      _ = Multiset.count x.norm.natAbs (3 • _) := by rw [factorsOddPrimeOrFour.pow _ _ this]
      _ = 3 * _ := Multiset.count_nsmul x.norm.natAbs _ _

    swap
    show
      Multiset.countP (Eq x.norm.natAbs) (Multiset.map (Int.natAbs ∘ Zsqrtd.norm) f) =
        Multiset.countP (Eq x.norm.natAbs) ((factorsOddPrimeOrFour a.norm.natAbs))
    congr 1
    · rw [factorsOddPrimeOrFour.unique hcoprime]
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        exact (h2 y hy).2.2
      · rw [← Multiset.map_map, prod_map_natAbs, prod_map_norm]
        cases' h1 with h1 h1 <;> rw [h1]
        rw [Zsqrtd.norm_neg]
    have h2x := h2 x hx
    refine' ⟨fun h => by rw [h], fun h => _⟩
    rw [← Int.associated_iff_natAbs] at h
    have hassoc := factorization'.associated'_of_norm_associated hcoprime hx HA h
    have eq_or_eq_conj := (eq_or_eq_conj_iff_associated'_of_nonneg h2x.1 (h2 A HA).1).mp hassoc
    refine' eq_or_eq_conj.resolve_right fun H => _
    apply no_conj f
    · intro HH
      apply h2x.2.1
      rw [Zsqrt3.isUnit_iff] at HH
      exact HH.2
    · cases' h1 with h1 h1 <;> rw [h1] at hcoprime
      · exact hcoprime
      · rwa [← IsCoprime.neg_neg_iff, ← Zsqrtd.neg_im, ← Zsqrtd.neg_re]
    · refine' ⟨hx, _⟩
      rwa [H, star_star]

theorem step5
    -- lemma page 54
    (a : ℤ√(-3))
    (r : ℕ) (hcoprime : IsCoprime a.re a.im) (hcube : r ^ 3 = a.norm.natAbs) : ∃ p : ℤ√(-3), a = p ^ 3 :=
  by
  obtain ⟨f, hf⟩ := step5' a r hcoprime hcube
  obtain ⟨h1, -⟩ := factorization'_prop hcoprime
  cases h1 with
  | inl h1 =>
    use f.prod
    rw [h1, hf, Multiset.prod_nsmul]
  | inr h1 =>
    use -f.prod
    rw [h1, hf, Multiset.prod_nsmul, Odd.neg_pow]
    norm_num; decide

theorem step6 (a b r : ℤ) (hcoprime : IsCoprime a b) (hcube : r ^ 3 = a ^ 2 + 3 * b ^ 2) :
    ∃ p q, a = p ^ 3 - 9 * p * q ^ 2 ∧ b = 3 * p ^ 2 * q - 3 * q ^ 3 :=
  by
  set A : ℤ√(-3) := ⟨a, b⟩ with hA
  have hcube' : r.natAbs ^ 3 = A.norm.natAbs :=
    by
    rw [← Int.natAbs_pow]
    apply congr_arg
    simp only [hcube, Zsqrtd.norm_def, hA]
    ring
  obtain ⟨p, hp⟩ := step5 A r.natAbs hcoprime hcube'
  use p.re, p.im
  simp only [Zsqrtd.ext_iff, pow_succ', pow_two, Zsqrtd.mul_re, Zsqrtd.mul_im] at hp
  convert hp using 2 <;> simp <;> ring
