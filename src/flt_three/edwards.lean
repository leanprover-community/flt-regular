/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import data.int.basic
import data.int.parity
import tactic
import .primes
import .spts
import .odd_prime_or_four

lemma zsqrtd.associated_norm_of_associated {d : ℤ} {f g : ℤ√d}
  (h : associated f g) : associated f.norm g.norm :=
begin
  obtain ⟨u, rfl⟩ := h,
  have := (zsqrtd.is_unit_iff_norm_is_unit ↑u).mp u.is_unit,
  rw [zsqrtd.norm_mul],
  exact (associated_mul_unit_right (zsqrtd.norm f) _ this),
end

lemma odd_prime_or_four.im_ne_zero
  {p : ℤ√-3}
  (h: odd_prime_or_four p.norm)
  (hcoprime: is_coprime p.re p.im) :
  p.im ≠ 0 :=
begin
  intro H,
  rw [zsqrtd.norm_def, H, mul_zero, sub_zero, ←pow_two] at h,
  obtain h|⟨hp, hodd⟩ := h,
  { rw [H, is_coprime_zero_right, int.is_unit_iff_abs_eq] at hcoprime,
    rw [←sq_abs, hcoprime] at h,
    norm_num at h },
  { exact pow_not_prime one_lt_two.ne' hp }
end

lemma zsqrt3.is_unit_iff {z : ℤ√-3} : is_unit z ↔ abs z.re = 1 ∧ z.im = 0 :=
begin
  rw [←zsqrtd.norm_eq_one_iff, ←int.coe_nat_inj', int.coe_nat_one,
    int.nat_abs_of_nonneg (zsqrtd.norm_nonneg (by norm_num) z)],
  refine ⟨spts.eq_one, λ h, _⟩,
  rw [zsqrtd.norm_def, h.2, mul_zero, sub_zero, ←sq, ←sq_abs, h.1, one_pow]
end

lemma zsqrt3.coe_of_is_unit {z : ℤ√-3} (h : is_unit z) : ∃ u : units ℤ, z = u :=
begin
  obtain ⟨u, hu⟩ := zsqrt3.is_unit_iff.mp h,
  obtain ⟨v, hv⟩ : is_unit z.re,
  { rwa int.is_unit_iff_abs_eq },
  use v,
  rw [zsqrtd.ext, hu, ←hv],
  simp only [zsqrtd.coe_int_re, and_true, eq_self_iff_true, coe_coe, zsqrtd.coe_int_im],
end

lemma zsqrt3.coe_of_is_unit' {z : ℤ√-3} (h : is_unit z) : ∃ u : ℤ, z = u ∧ abs u = 1 :=
begin
  obtain ⟨u, hu⟩ := zsqrt3.coe_of_is_unit h,
  refine ⟨u, _, _⟩,
  { rw [hu, coe_coe] },
  { exact int.is_unit_iff_abs_eq.mp u.is_unit },
end

lemma odd_prime_or_four.factors
  (a : ℤ√-3)
  (x : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hx : odd_prime_or_four x)
  (hfactor : x ∣ a.norm) :
  ∃ c : ℤ√-3, abs x = c.norm ∧ 0 ≤ c.re ∧ c.im ≠ 0 :=
begin
  obtain rfl|⟨hprime, hodd⟩ := hx,
  { refine ⟨⟨1, 1⟩, _, zero_le_one, one_ne_zero⟩,
    simp only [zsqrtd.norm_def, mul_one, abs_of_pos, zero_lt_four, sub_neg_eq_add],
    norm_num },
  { obtain ⟨c, hc⟩ := factors a x hcoprime hodd hfactor,
    rw hc,
    apply zsqrtd.exists c,
    intro H,
    apply pow_not_prime one_lt_two.ne',
    convert hprime.abs,
    rwa [zsqrtd.norm_def, H, mul_zero, sub_zero, ←pow_two, eq_comm] at hc }
end

lemma step1a
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (heven : even a.norm) :
  odd a.re ∧ odd a.im :=
begin
  rw [int.odd_iff_not_even, int.odd_iff_not_even],
  have : even a.re ↔ even a.im,
  { simpa [zsqrtd.norm_def] with parity_simps using heven },
  apply (iff_iff_and_or_not_and_not.mp this).resolve_left,
  rw [even_iff_two_dvd, even_iff_two_dvd],
  rintro ⟨hre, him⟩,
  have := hcoprime.is_unit_of_dvd' hre him,
  rw is_unit_iff_dvd_one at this,
  norm_num at this,
end

lemma step1
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (heven : even a.norm) :
  ∃ u : ℤ√-3, (a = ⟨1, 1⟩ * u ∨ a = ⟨1, -1⟩ * u) :=
begin
  obtain ⟨ha, hb⟩ := step1a hcoprime heven,
  obtain hdvd|hdvd := int.four_dvd_add_or_sub_of_odd ha hb,
  { obtain ⟨v, hv⟩ := hdvd,
    rw ←eq_sub_iff_add_eq at hv,
    use ⟨v - a.im, v⟩,
    right,
    rw [zsqrtd.ext, hv, zsqrtd.mul_re, zsqrtd.mul_im],
    dsimp only,
    split; ring },
  { obtain ⟨v, hv⟩ := hdvd,
    rw sub_eq_iff_eq_add at hv,
    use ⟨a.im + v, -v⟩,
    left,
    rw [zsqrtd.ext, hv, zsqrtd.mul_re, zsqrtd.mul_im],
    dsimp only,
    split; ring },
end

lemma step1'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (heven : even a.norm) :
  ∃ u : ℤ√-3,
    is_coprime u.re u.im ∧
    a.norm = 4 * u.norm :=
begin
  obtain ⟨u', hu'⟩ := step1 hcoprime heven,
  refine ⟨u', _, _⟩,
  { apply zsqrtd.coprime_of_dvd_coprime hcoprime,
    obtain (rfl|rfl) := hu'; apply dvd_mul_left },
  { cases hu';
    { rw [hu', zsqrtd.norm_mul], congr } }
end

lemma step1'' {a p : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (hp : p.norm = 4)
  (hq : p.im ≠ 0)
  (heven : even a.norm) :
  ∃ (u : ℤ√-3),
    is_coprime u.re u.im ∧
      (a = p * u ∨ a = p.conj * u) ∧ a.norm = 4 * u.norm :=
begin
  obtain ⟨u, h2⟩ := step1 hcoprime heven,
  set q : ℤ√-3 := ⟨1, 1⟩,
  replace h2 : a = q * u ∨ a = q.conj * u := h2,
  obtain ⟨hp', hq'⟩ := spts.four hp hq,
  refine ⟨p.re * u, _, _, _⟩,
  { rw ←int.is_unit_iff_abs_eq at hp',
    rwa [zsqrtd.smul_re, zsqrtd.smul_im, is_coprime_mul_unit_left hp'],
    apply zsqrtd.coprime_of_dvd_coprime hcoprime,
    obtain (rfl|rfl) := h2; apply dvd_mul_left },
  { rw (abs_eq $ zero_le_one' ℤ) at hp' hq',
    cases hp',
    { have h4 : p = q ∨ p = q.conj,
      { apply or.imp _ _ hq';
        { intro h5, simp [zsqrtd.ext, hp', h5] } },
      simp only [hp', one_mul, int.cast_one],
      cases h4; simp [h4, h2, zsqrtd.conj_conj, or_comm] },
    { have h4 : p = -q ∨ p = -q.conj,
      { apply or.imp _ _ hq'.symm,
        { intro h5, simp [zsqrtd.ext, hp', h5] },
        { intro h5, simp [zsqrtd.ext, hp', h5] } },
      simp only [hp', one_mul, zsqrtd.norm_neg, int.cast_one, int.cast_neg, neg_one_mul],
      cases h4,
      simp [h4, h2],
      simp [h4, h2, or_comm] } },
  { rw [zsqrtd.norm_mul, zsqrtd.norm_int_cast, ←sq, ←sq_abs, hp', one_pow, one_mul],
    cases h2;
    { rw [h2, zsqrtd.norm_mul], congr } },
end

lemma step2
  {a p : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (hdvd : p.norm ∣ a.norm)
  (hpprime : prime p.norm) :
  ∃ u : ℤ√-3,
    is_coprime u.re u.im ∧
    (a = p * u ∨ a = p.conj * u) ∧
    a.norm = p.norm * u.norm :=
begin
  obtain ⟨u', h, h'⟩ := spts.mul_of_dvd'' hdvd hpprime,
  refine ⟨u', _, h, h'⟩,
  apply zsqrtd.coprime_of_dvd_coprime hcoprime,
  obtain (rfl|rfl) := h; apply dvd_mul_left
end

lemma step1_2
  {a p : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (hdvd : p.norm ∣ a.norm)
  (hp : odd_prime_or_four p.norm)
  (hq : p.im ≠ 0) :
  ∃ u : ℤ√-3,
    is_coprime u.re u.im ∧
    (a = p * u ∨ a = p.conj * u) ∧
    a.norm = p.norm * u.norm :=
begin
  obtain hp|⟨hpprime, hpodd⟩ := hp,
  { rw hp at hdvd ⊢,
    have heven : even a.norm,
    { apply even_iff_two_dvd.mpr (dvd_trans _ hdvd),
      norm_num },
    exact step1'' hcoprime hp hq heven },
  { apply step2 hcoprime hdvd hpprime }
end

lemma odd_prime_or_four.factors'
  {a : ℤ√-3}
  (h2 : a.norm ≠ 1)
  (hcoprime : is_coprime a.re a.im) :
  ∃ (u q : ℤ√-3),
    0 ≤ q.re ∧
    q.im ≠ 0 ∧
    odd_prime_or_four q.norm ∧
    a = q * u ∧
    is_coprime u.re u.im ∧
    u.norm < a.norm :=
begin
  have h2 : 2 < a.norm,
  { apply lt_of_le_of_ne _ (spts.not_two _).symm,
    rw [←one_mul (2 : ℤ), mul_two, int.add_one_le_iff],
    apply lt_of_le_of_ne _ h2.symm,
    rw [←int.sub_one_lt_iff, sub_self],
    exact spts.pos_of_coprime' hcoprime },
  obtain ⟨p, hpdvd, hp⟩ := odd_prime_or_four.exists_and_dvd h2,
  obtain ⟨q', hcd, hc, hd⟩ := odd_prime_or_four.factors a p hcoprime hp hpdvd,
  rw [←abs_dvd, hcd] at hpdvd,
  have hp' := hp.abs,
  rw hcd at hp',

  obtain ⟨u, huvcoprime, huv, huvdvd⟩ := step1_2 hcoprime hpdvd hp' hd,
  use u,
  cases huv; [use q', use q'.conj];
  try { rw [zsqrtd.conj_re, zsqrtd.conj_im, neg_ne_zero, zsqrtd.norm_conj] };
  use [hc, hd, hp', huv, huvcoprime];
  { rw [huvdvd, lt_mul_iff_one_lt_left (spts.pos_of_coprime' huvcoprime), ←hcd],
    exact hp.one_lt_abs },
end

lemma step3
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  :
  ∃ f : multiset ℤ√-3,
    (a = f.prod ∨ a = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
  :=
begin
  suffices : ∀ n : ℕ, a.norm.nat_abs = n →
    ∃ f : multiset ℤ√-3,
    (a = f.prod ∨ a = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm,
  { exact this a.norm.nat_abs rfl },

  intros n hn,
  induction n using nat.strong_induction_on with n ih generalizing a,
  dsimp only at ih,

  cases eq_or_ne a.norm 1 with h h,
  { use 0,
    split,
    { simp only [multiset.prod_zero, spts.eq_one' h] },
    { intros pq hpq,
      exact absurd hpq (multiset.not_mem_zero _) } },
  { obtain ⟨U, q, hc, hd, hp, huv, huvcoprime, descent⟩ := odd_prime_or_four.factors'
      h hcoprime,
    replace descent := int.nat_abs_lt_nat_abs_of_nonneg_of_lt (zsqrtd.norm_nonneg (by norm_num) _) descent,
    rw [hn] at descent,
    obtain ⟨g, hgprod, hgfactors⟩ := ih U.norm.nat_abs descent huvcoprime rfl,
    refine ⟨q ::ₘ g, _, _⟩,
    { simp only [huv, multiset.prod_cons, ←mul_neg],
      exact or.imp (congr_arg _) (congr_arg _) hgprod },
    { rintros pq hpq,
      rw multiset.mem_cons at hpq,
      obtain rfl|ind := hpq,
      { exact ⟨hc, hd, hp⟩ },
      { exact hgfactors pq ind } } },
end

lemma step4_3
  {p p' : ℤ√-3}
  (hcoprime : is_coprime p.re p.im)
  (hcoprime' : is_coprime p'.re p'.im)
  (h : odd_prime_or_four p.norm)
  (heq : p.norm = p'.norm) :
  abs p.re = abs p'.re ∧ abs p.im = abs p'.im :=
begin
  have hdvd : p'.norm ∣ p.norm,
  { rw heq },
  have him : p'.im ≠ 0,
  { apply odd_prime_or_four.im_ne_zero _ hcoprime',
    rwa [←heq] },
  obtain ⟨u, hcoprime'', (H|H), h1⟩ := step1_2 hcoprime hdvd (by rwa ←heq) him;
  { rw heq at h1,
    have := int.eq_one_of_mul_eq_self_right (spts.ne_zero_of_coprime' _ hcoprime') h1.symm,
    obtain ⟨ha, hb⟩ := spts.eq_one this,
    simp only [hb, zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im, add_zero, zero_add, mul_zero] at H,
    rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one],
    try { rw [zsqrtd.conj_re, zsqrtd.conj_im, abs_neg] },
    split; refl },
end

lemma prod_map_norm {d : ℤ} {s : multiset ℤ√d} :
  (s.map zsqrtd.norm).prod = zsqrtd.norm s.prod :=
multiset.prod_hom s (zsqrtd.norm_monoid_hom : ℤ√d →* ℤ)

lemma factors_unique_prod : ∀{f g : multiset ℤ√-3},
  (∀x∈f, odd_prime_or_four (zsqrtd.norm x)) →
  (∀x∈g, odd_prime_or_four (zsqrtd.norm x)) →
  (associated f.prod.norm g.prod.norm) →
  multiset.rel associated (f.map zsqrtd.norm) (g.map zsqrtd.norm) :=
begin
  intros f g hf hg hassoc,
  apply factors_unique_prod',
  { intros x hx,
    rw multiset.mem_map at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    exact hf y hy },
  { intros x hx,
    rw multiset.mem_map at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    exact hg y hy },
  { rwa [prod_map_norm, prod_map_norm] },
end

noncomputable def factorization'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  : multiset ℤ√-3
 := classical.some (step3 hcoprime)

lemma factorization'_prop
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  (a = (factorization' hcoprime).prod ∨ a = - (factorization' hcoprime).prod) ∧
    ∀ pq : ℤ√-3, pq ∈ (factorization' hcoprime) →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm :=
classical.some_spec (step3 hcoprime)

lemma factorization'.coprime_of_mem
  {a b : ℤ√-3} (h : is_coprime a.re a.im) (hmem : b ∈ factorization' h) :
  is_coprime b.re b.im :=
begin
  obtain ⟨h1, -⟩ := factorization'_prop h,
  set f := factorization' h,
  apply zsqrtd.coprime_of_dvd_coprime h,
  apply (multiset.dvd_prod hmem).trans,
  cases h1; simp only [h1, dvd_neg],
end

lemma no_conj
  (s : multiset ℤ√-3)
  {p : ℤ√-3}
  (hp : ¬ is_unit p)
  (hcoprime : is_coprime s.prod.re s.prod.im) :
  ¬(p ∈ s ∧ p.conj ∈ s) :=
begin
  contrapose! hp,
  obtain ⟨h1, h2⟩ := hp,
  by_cases him : p.im = 0,
  { obtain ⟨t, rfl⟩ := multiset.exists_cons_of_mem h1,
    rw multiset.prod_cons at hcoprime,
    simp only [him, add_zero, zero_mul, zsqrtd.mul_im, zsqrtd.mul_re, mul_zero] at hcoprime,
    rw zsqrt3.is_unit_iff,
    simp only [him, and_true, eq_self_iff_true],
    rw ←int.is_unit_iff_abs_eq,
    apply is_coprime.is_unit_of_dvd' hcoprime; apply dvd_mul_right },
  { have : p.conj ≠ p,
    { rw [ne.def, zsqrtd.ext],
      rintro ⟨-, H⟩,
      apply him,
      apply eq_zero_of_neg_eq,
      rwa [zsqrtd.conj_im] at H },
    obtain ⟨t1, rfl⟩ := multiset.exists_cons_of_mem h1,
    have : p.conj ∈ t1,
    { rw multiset.mem_cons at h2,
      exact h2.resolve_left this },
    obtain ⟨t2, rfl⟩ := multiset.exists_cons_of_mem this,
    rw [multiset.prod_cons, multiset.prod_cons, ←mul_assoc, ←zsqrtd.norm_eq_mul_conj] at hcoprime,
    rw zsqrtd.is_unit_iff_norm_is_unit,
    apply is_coprime.is_unit_of_dvd' hcoprime;
    simp only [add_zero, zsqrtd.coe_int_re, zero_mul, dvd_mul_right, zsqrtd.mul_re, mul_zero,
      zsqrtd.mul_im, zsqrtd.coe_int_im] },
end

def associated' (x y : ℤ√-3) : Prop := associated x y ∨  associated x y.conj

@[refl] theorem associated'.refl (x : ℤ√-3) : associated' x x := or.inl (by refl)

lemma associated'.norm_eq
  {x y : ℤ√-3}
  (h : associated' x y) :
  x.norm = y.norm :=
begin
  cases h; simp only [zsqrtd.norm_eq_of_associated (by norm_num) h, zsqrtd.norm_conj],
end

lemma associated'_of_abs_eq {x y : ℤ√-3} (hre : abs x.re = abs y.re) (him : abs x.im = abs y.im) :
  associated' x y :=
begin
  rw abs_eq_abs at hre him,
  cases hre with h1 h1;
  cases him with h2 h2;
  [{ left, use 1}, {right, use 1}, {right, use -1}, {left, use -1}];
  simp only [units.coe_one, mul_one, units.coe_neg_one, mul_neg_one, zsqrtd.ext, zsqrtd.neg_im,
    zsqrtd.neg_re, h1, h2, neg_neg, zsqrtd.conj_re, zsqrtd.conj_im, eq_self_iff_true, and_self],
end

lemma associated'_of_associated_norm {x y : ℤ√-3} (h : associated (zsqrtd.norm x) (zsqrtd.norm y))
  (hx : is_coprime x.re x.im)
  (hy : is_coprime y.re y.im)
  (h' : odd_prime_or_four x.norm) :
  associated' x y :=
begin
  have heq : x.norm = y.norm,
  { have hd : (-3 : ℤ) ≤ 0,
    { norm_num },
    exact int.eq_of_associated_of_nonneg h (zsqrtd.norm_nonneg hd _) (zsqrtd.norm_nonneg hd _) },
  obtain ⟨hre, him⟩ := step4_3 hx hy h' heq,
  exact associated'_of_abs_eq hre him,
end

lemma factorization'.associated'_of_norm_eq
  {a b c : ℤ√-3} (h : is_coprime a.re a.im)
  (hbmem : b ∈ factorization' h) (hcmem : c ∈ factorization' h)
  (hnorm : b.norm = c.norm) :
  associated' b c :=
begin
  apply associated'_of_associated_norm,
  { rw hnorm },
  { exact factorization'.coprime_of_mem h hbmem },
  { exact factorization'.coprime_of_mem h hcmem },
  { exact ((factorization'_prop h).2 b hbmem).2.2 },
end

lemma factors_unique
  {f g : multiset ℤ√-3}
  (hf : ∀x∈f, odd_prime_or_four (zsqrtd.norm x))
  (hf' : ∀x∈f, is_coprime (zsqrtd.re x) (zsqrtd.im x))
  (hg : ∀x∈g, odd_prime_or_four (zsqrtd.norm x))
  (hg' : ∀x∈g, is_coprime (zsqrtd.re x) (zsqrtd.im x))
  (h : associated f.prod g.prod) :
  multiset.rel associated' f g :=
begin
  have p : ∀ (x : ℤ√-3) (hx : x ∈ f) (y : ℤ√-3) (hy : y ∈ g),
    associated x.norm y.norm → associated' x y,
  { intros x hx y hy hxy,
    apply associated'_of_associated_norm hxy,
    { exact hf' x hx },
    { exact hg' y hy },
    { exact hf x hx } },

  refine multiset.rel.mono _ p,
  rw ←multiset.rel_map,
  apply factors_unique_prod hf hg,
  exact zsqrtd.associated_norm_of_associated h,
end
lemma factors_2_even'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  even (even_factor_exp a.norm) :=
begin
  induction hn : a.norm.nat_abs using nat.strong_induction_on with n ih generalizing a,
  dsimp only at ih,
  by_cases hparity : even a.norm,
  { obtain ⟨u, huvcoprime, huvprod⟩ := step1' hcoprime hparity,
    have huv := spts.ne_zero_of_coprime' _ huvcoprime,
    rw [huvprod, factors_2_even huv, nat.even_add],
    apply iff_of_true even_two,
    apply ih _ _ huvcoprime rfl,
    rw [←hn, huvprod, int.nat_abs_mul, lt_mul_iff_one_lt_left (int.nat_abs_pos_of_ne_zero huv)],
    norm_num },
  { convert even_zero,
    simp only [even_factor_exp, multiset.count_eq_zero, hn],
    contrapose! hparity with hfactor,
    rw even_iff_two_dvd,
    exact unique_factorization_monoid.dvd_of_mem_normalized_factors hfactor }
end

lemma factors_odd_prime_or_four.unique
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (hf' : ∀x∈f, (0 : ℤ) ≤ x)
  (hassoc : associated f.prod a.norm) :
  f = (factors_odd_prime_or_four a.norm) :=
factors_odd_prime_or_four.unique' hf hf' (spts.pos_of_coprime' hcoprime) (factors_2_even' hcoprime)
  hassoc

lemma eq_or_eq_conj_of_associated_of_re_zero
  {x A : ℤ√-3}
  (hx : x.re = 0)
  (h : associated x A) :
  x = A ∨ x = A.conj :=
begin
  obtain ⟨u, hu⟩ := h,
  obtain ⟨v, hv1, hv2⟩ := zsqrt3.coe_of_is_unit' u.is_unit,
  have hA : A.re = 0,
  { simp only [←hu, hv1, hx, add_zero, zero_mul, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] },
  rw (abs_eq $ zero_le_one' ℤ) at hv2,
  cases hv2 with hv2 hv2,
  { left,
    simpa only [hv1, hv2, mul_one, int.cast_one] using hu },
  { right,
    simp only [hv1, hv2, mul_one, int.cast_one, mul_neg, int.cast_neg] at hu,
    simp only [←hu, hx, zsqrtd.conj_neg, zsqrtd.ext, zsqrtd.neg_re, zsqrtd.neg_im, zsqrtd.conj_re,
      zsqrtd.conj_im, neg_neg, neg_zero, eq_self_iff_true, and_self] }
end

lemma eq_or_eq_conj_iff_associated'_of_nonneg
  {x A : ℤ√-3}
  (hx : 0 ≤ x.re)
  (hA : 0 ≤ A.re) :
  associated' x A ↔ (x = A ∨ x = A.conj) :=
begin
  split,
  { rintro (⟨u, hu⟩|⟨u, hu⟩); obtain ⟨v, hv1, hv2⟩ := zsqrt3.coe_of_is_unit' u.is_unit,
    -- associated x A
    { by_cases hxre : x.re = 0,
      { apply eq_or_eq_conj_of_associated_of_re_zero hxre ⟨u, hu⟩ },
      { rw hv1 at hu,
        rw (abs_eq $ zero_le_one' ℤ) at hv2,
        cases hv2 with habsv habsv,
        { left,
          rw [←hu, habsv, int.cast_one, mul_one] },
        { exfalso,
          simp only [habsv, mul_one, int.cast_one, mul_neg, int.cast_neg] at hu,
          apply lt_irrefl (0 : ℤ),
          calc 0 ≤ A.re : hA
          ... = -x.re : _
          ... < 0 : _,
          { simp only [←hu, zsqrtd.neg_re] },
          { simp only [neg_neg_iff_pos],
            exact lt_of_le_of_ne hx (ne.symm hxre) } } } },

    -- associated x A.conj
    { by_cases hxre : x.re = 0,
      { convert (eq_or_eq_conj_of_associated_of_re_zero hxre ⟨u, hu⟩).symm,
        rw zsqrtd.conj_conj },
      { rw hv1 at hu,
        rw (abs_eq $ zero_le_one' ℤ) at hv2,
        cases hv2 with habsv habsv,
        { right,
          rw [←hu, habsv, int.cast_one, mul_one] },
        { exfalso,
          simp only [habsv, mul_one, int.cast_one, mul_neg, int.cast_neg] at hu,
          apply lt_irrefl (0 : ℤ),
          calc 0 ≤ A.re : hA
          ... = -x.re : _
          ... < 0 : _,
          { rw [←zsqrtd.conj_conj A, ←hu],
            simp only [zsqrtd.conj_re, zsqrtd.neg_re] },
          { simp only [neg_neg_iff_pos],
            apply lt_of_le_of_ne hx (ne.symm hxre) } } } } },
  { rintro (rfl|rfl),
    { refl },
    { right, refl } },
end

lemma step5' -- lemma page 54
  (a : ℤ√-3)
  (r : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hcube : r ^ 3 = a.norm) :
  ∃ g : multiset ℤ√-3, factorization' hcoprime = 3 • g :=
begin
  classical,

  obtain ⟨h1, h2⟩ := factorization'_prop hcoprime,
  set f := factorization' hcoprime with hf,
  apply multiset.exists_smul_of_dvd_count,

  intros x hx,
  convert dvd_mul_right _ _,
  have : even (even_factor_exp r),
  { suffices : even (3 * even_factor_exp r),
    { rw nat.even_mul at this,
      apply this.resolve_left,
      norm_num },
    rw [←even_factor_exp.pow r 3, hcube],
    exact factors_2_even' hcoprime },
  calc multiset.count x f
      = multiset.card (multiset.filter (eq x) f) :
        by rw [multiset.count, multiset.countp_eq_card_filter]
  ... = multiset.card (multiset.filter (λ (a : ℤ√-3), eq x.norm a.norm) f) :
        congr_arg _ (multiset.filter_congr (λ A HA, _))
  ... = multiset.countp (eq x.norm) (multiset.map zsqrtd.norm f) :
        (multiset.countp_map zsqrtd.norm f (eq x.norm)).symm
  ... = multiset.countp (eq x.norm) (factors_odd_prime_or_four a.norm) : _
  ... = multiset.count x.norm (factors_odd_prime_or_four a.norm) : by rw multiset.count
  ... = multiset.count x.norm (factors_odd_prime_or_four (r ^ 3)) : by rw hcube
  ... = multiset.count x.norm (3 • _) : congr_arg _ $ factors_odd_prime_or_four.pow _ _ this
  ... = 3 * _ : multiset.count_nsmul x.norm _ _,

  show multiset.countp (eq x.norm) (multiset.map zsqrtd.norm f) =
    multiset.countp (eq x.norm) (factors_odd_prime_or_four a.norm),
  congr',
  { apply factors_odd_prime_or_four.unique hcoprime,
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      exact (h2 y hy).2.2 },
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      apply zsqrtd.norm_nonneg,
      norm_num },
    { rw [prod_map_norm],
      cases h1; rw [h1],
      rw zsqrtd.norm_neg } },

  have h2x := h2 x hx,

  refine ⟨congr_arg _, λ h, _⟩,
  have hassoc := factorization'.associated'_of_norm_eq hcoprime hx HA h,
  have eq_or_eq_conj := (eq_or_eq_conj_iff_associated'_of_nonneg h2x.1 (h2 A HA).1).mp hassoc,
  refine eq_or_eq_conj.resolve_right (λ H, _),
  apply no_conj f,
  { intro HH,
    apply h2x.2.1,
    rw [zsqrt3.is_unit_iff] at HH,
    exact HH.2 },
  { cases h1; rw h1 at hcoprime,
    { exact hcoprime },
    { rwa [←is_coprime.neg_neg_iff, ←zsqrtd.neg_im, ←zsqrtd.neg_re] } },
  { refine ⟨hx, _⟩,
    rwa [H, zsqrtd.conj_conj] },
end

lemma step5 -- lemma page 54
  (a : ℤ√-3)
  (r : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hcube : r ^ 3 = a.norm) :
  ∃ p : ℤ√-3, a = p ^ 3 :=
begin
  obtain ⟨f, hf⟩ := step5' a r hcoprime hcube,
  obtain ⟨h1, -⟩ := factorization'_prop hcoprime,
  cases h1,
  { use f.prod,
    rw [h1, hf, multiset.prod_nsmul] },
  { use -f.prod,
    rw [h1, hf, multiset.prod_nsmul, neg_pow_bit1] },
end

lemma step6
  (a b r : ℤ)
  (hcoprime : is_coprime a b)
  (hcube : r ^ 3 = a ^ 2 + 3 * b ^ 2)
  :
  ∃ p q,
    a = p ^ 3 - 9 * p * q ^ 2 ∧
    b = 3 * p ^ 2 * q - 3 * q ^ 3
  :=
begin
  set A : ℤ√-3 := ⟨a, b⟩,
  have hcube' : r ^ 3 = A.norm,
  { simp only [hcube, zsqrtd.norm_def, A], ring },
  obtain ⟨p, hp⟩ := step5 A r hcoprime hcube',
  use [p.re, p.im],
  simp only [zsqrtd.ext, pow_succ', pow_two, zsqrtd.mul_re, zsqrtd.mul_im] at hp,
  convert hp; ring,
end
