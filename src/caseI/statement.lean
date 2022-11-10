import caseI.aux_lemmas

open finset nat is_cyclotomic_extension ideal polynomial int basis flt_regular.caseI

open_locale big_operators number_field

namespace flt_regular

variables {p : ℕ} [hpri : fact p.prime]

local notation `P` := (⟨p, hpri.out.pos⟩ : ℕ+)
local notation `K` := cyclotomic_field P ℚ
local notation `R` := 𝓞 K

namespace caseI

/-- Statement of case I with additional assumptions. -/
def slightly_easier : Prop := ∀ ⦃a b c : ℤ⦄ {p : ℕ} [hpri : fact p.prime]
  (hreg : @is_regular_prime p hpri) (hp5 : 5 ≤ p)
  (hgcd : ({a, b, c} : finset ℤ).gcd id = 1)
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

/-- Statement of case I. -/
def statement : Prop := ∀ ⦃a b c : ℤ⦄ {p : ℕ} [hpri : fact p.prime]
  (hreg : @is_regular_prime p hpri) (caseI : ¬ ↑p ∣ a * b * c),
  a ^ p + b ^ p ≠ c ^ p

lemma may_assume : slightly_easier → statement :=
begin
  intro Heasy,
  intros a b c p hpri hreg hI H,
  have hodd : p ≠ 2,
  { intro h,
    rw [h] at H hI,
    refine hI _,
    refine has_dvd.dvd.mul_left _ _,
    simp only [coe_nat_bit0, algebra_map.coe_one, ← even_iff_two_dvd] at ⊢ hI,
    rw [← int.odd_iff_not_even] at hI,
    rw [← int.even_pow' (show 2 ≠ 0, by norm_num), ← H],
    exact (odd.of_mul_left (odd.of_mul_left hI)).pow.add_odd
      (odd.of_mul_right (odd.of_mul_left hI)).pow },
  have hprod : a * b * c ≠ 0,
  { intro h,
    simpa [h] using hI },
  have hp5 : 5 ≤ p,
  { by_contra' habs,
    have : p ∈ finset.Ioo 2 5 := finset.mem_Icc.2 ⟨nat.lt_of_le_and_ne hpri.out.two_le hodd.symm,
      by linarith⟩,
    fin_cases this,
    { exact may_assume.p_ne_three hprod H rfl },
    { rw [show 4 = 2 * 2, from rfl] at hpri,
      refine nat.not_prime_mul one_lt_two one_lt_two hpri.out } },
  rcases may_assume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩,
  let d := ({a, b, c} : finset ℤ).gcd id,
  have hdiv : ¬↑p ∣ (a / d) * (b / d) * (c / d),
  { have hadiv : d ∣ a := gcd_dvd (by simp),
    have hbdiv : d ∣ b := gcd_dvd (by simp),
    have hcdiv : d ∣ c := gcd_dvd (by simp),
    intro hdiv,
    replace hdiv := dvd_mul_of_dvd_right hdiv ((d * d) * d),
    rw [mul_assoc, ← mul_assoc d, ← mul_assoc d, int.mul_div_cancel' hadiv, mul_assoc,
      mul_comm a, mul_assoc (b / d), ← mul_assoc _ (b / d), int.mul_div_cancel' hbdiv,
      mul_comm, mul_assoc, mul_assoc, int.div_mul_cancel hcdiv, mul_comm, mul_assoc,
      mul_comm c, ← mul_assoc] at hdiv,
    exact hI hdiv },
  obtain ⟨X, Y, Z, H1, H2, H3, H4, H5⟩ := a_not_cong_b hpri.out hp5 hprodxyx Hxyz hunit hdiv,
  exactI Heasy hreg hp5 H2 H3 (λ hfin, H5 hfin) H1
end

end caseI

lemma ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
  (hgcd : ({a, b, c} : finset ℤ).gcd id = 1) : is_coprime a b  :=
begin
  rw [← gcd_eq_one_iff_coprime],
  by_contra' h,
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h,
  replace hqpri : prime (q : ℤ) := prime_iff_nat_abs_prime.2 (by simp [hqpri]),
  obtain ⟨n, hn⟩ := hq,
  have haq : ↑q ∣ a,
  { obtain ⟨m, hm⟩ := int.gcd_dvd_left a b,
    exact ⟨n * m, by { rw [hm, hn], simp [mul_assoc] }⟩ },
  have hbq : ↑q ∣ b,
  { obtain ⟨m, hm⟩ := int.gcd_dvd_right a b,
    exact ⟨n * m, by { rw [hm, hn], simp [mul_assoc] }⟩ },
  have hcq : ↑q ∣ c,
  { suffices : ↑q ∣ c ^ p,
    { exact hqpri.dvd_of_dvd_pow this },
    rw [← H],
    exact dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero) },
  have Hq : ↑q ∣ ({a, b, c} : finset ℤ).gcd id,
  { refine dvd_gcd (λ x hx, _),
    simp only [mem_insert, mem_singleton] at hx,
    rcases hx with H | H | H;
    simpa [H] },
  rw [hgcd] at Hq,
  exact hqpri.not_unit (is_unit_of_dvd_one _ Hq)
end

theorem exists_ideal {a b c : ℤ} (h5p : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p)
  (hgcd : ({a, b, c} : finset ℤ).gcd id = 1) (caseI : ¬ ↑p ∣ a * b * c)
  {ζ : R} (hζ : ζ ∈ nth_roots_finset p R) : ∃ I, span ({a + ζ * b} : set R) = I ^ p :=
begin
  haveI : fact ((P : ℕ).prime) := ⟨hpri.out⟩,
  classical,
  have H₁ := congr_arg (algebra_map ℤ R) H,
  simp only [eq_int_cast, int.cast_add, int.cast_pow] at H₁,
  have hζ' := (zeta_spec P ℚ K).unit'_coe,
  rw [pow_add_pow_eq_prod_add_zeta_runity_mul
      (hpri.out.eq_two_or_odd.resolve_left $ λ h, by norm_num [h] at h5p) hζ'] at H₁,
  replace H₁ := congr_arg (λ x, span ({x} : set R)) H₁,
  simp only [span_singleton_prod, ← span_singleton_pow] at H₁,
  obtain ⟨I, hI⟩ := exists_eq_pow_of_prod_eq_pow p (span ({c} : set R)) (λ η₁ hη₁ η₂ hη₂ hη, _) H₁ ζ hζ,
  { exact ⟨I, hI⟩ },
  { exact flt_ideals_coprime h5p H (ab_coprime H hpri.out.ne_zero hgcd) hη₁ hη₂ hη caseI }
end

theorem is_principal {a b c : ℤ} {ζ : R} (hreg : is_regular_prime p) (hp5 : 5 ≤ p)
  (hgcd : ({a, b, c} : finset ℤ).gcd id = 1) (caseI : ¬ ↑p ∣ a * b * c)
  (H : a ^ p + b ^ p = c ^ p) (hζ : is_primitive_root ζ p) :
  ∃ (u : Rˣ) (α : R), ↑u * (α ^ p) = ↑a + ζ * ↑b :=
begin
  replace hζ := hζ.mem_nth_roots_finset hpri.out.pos,
  obtain ⟨I, hI⟩ := exists_ideal hp5 H hgcd caseI hζ,
  by_cases hIpzero : I ^ p = 0,
  { refine ⟨1, 0, _⟩,
    simp [hIpzero, zero_eq_bot, span_singleton_eq_bot] at hI,
    simp [hpri.out.pos, hI] },
  have hIzero : I ≠ 0,
  { intro hIzero,
    simp only [hIzero, zero_pow hpri.out.pos] at hIpzero,
    exact hIpzero rfl },
  have hIprin : I.is_principal,
  { have : class_group.mk0 ⟨_, mem_non_zero_divisors_of_ne_zero hIpzero⟩ = 1,
    { rw [class_group.mk0_eq_one_iff (mem_non_zero_divisors_of_ne_zero hIpzero)],
      exact ⟨⟨↑a + ζ * ↑b, hI.symm⟩⟩ },
    rw [← submonoid_class.mk_pow I (mem_non_zero_divisors_of_ne_zero hIzero), map_pow] at this,
    cases (dvd_prime hpri.out).1 (order_of_dvd_of_pow_eq_one this) with h1 habs,
    { exact (class_group.mk0_eq_one_iff _).1 (order_of_eq_one_iff.1 h1) },
    { exfalso,
      refine hpri.out.coprime_iff_not_dvd.1 hreg _,
      simp_rw [← habs],
      exact order_of_dvd_card_univ, } },
  obtain ⟨α, hα⟩ := hIprin,
  replace hα := congr_arg (λ J, J ^ p) hα,
  simp only [←hI, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hα,
  obtain ⟨u, hu⟩ := hα,
  refine ⟨u⁻¹, α, _⟩,
  rw [← hu, mul_comm _ ↑u, ← mul_assoc],
  simp
end

theorem ex_fin_div {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p)
  (hreg : is_regular_prime p) (hζ : is_primitive_root ζ p)
  (hgcd : ({a, b, c} : finset ℤ).gcd id = 1) (caseI : ¬ ↑p ∣ a * b * c)
  (H : a ^ p + b ^ p = c ^ p) :
  ∃ (k₁ k₂ : fin p), k₂ ≡ k₁ - 1 [ZMOD p] ∧ ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) :=
begin
  let ζ' := (ζ : K),
  have hζ' : is_primitive_root ζ' P := is_primitive_root.coe_submonoid_class_iff.2 hζ,
  have : ζ = (hζ'.unit' : R) := by simp only [is_primitive_root.unit', set_like.eta, units.coe_mk],
  have hP : P ≠ 2,
  { intro hP,
    rw [← pnat.coe_inj, pnat.mk_coe, pnat.coe_bit0, pnat.one_coe] at hP,
    norm_num [hP] at hp5 },
  haveI := (⟨hpri.out⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K := cyclotomic_field.is_cyclotomic_extension P ℚ,
  obtain ⟨u, α, hu⟩ := is_principal hreg hp5 hgcd caseI H hζ,
  rw [this, mul_comm _ ↑b, ← pow_one hζ'.unit'] at hu,
  obtain ⟨k, hk⟩ := @flt_regular.caseI.exists_int_sum_eq_zero P K _ _
    (by {convert diamond, by exact subsingleton.elim _ _ }) ζ hζ' hP _ a b 1 u α hu.symm,
  simp only [zpow_one, zpow_neg, coe_coe, pnat.mk_coe, mem_span_singleton, ← this] at hk,
  have hpcoe : (p : ℤ) ≠ 0 := by simp [hpri.out.ne_zero],
  refine ⟨⟨(2 * k % p).nat_abs, _⟩, ⟨((2 * k - 1) % p).nat_abs, _⟩, _, _⟩,
  repeat { rw [← nat_abs_of_nat p],
    refine nat_abs_lt_nat_abs_of_nonneg_of_lt (mod_nonneg _ hpcoe) _,
    rw [nat_abs_of_nat],
    exact mod_lt_of_pos _ (by simp [hpri.out.pos]) },
  { simp [nat_abs_of_nonneg (mod_nonneg _ hpcoe), ← zmod.int_coe_eq_int_coe_iff] },
  simp only [add_sub_assoc, sub_sub] at hk ⊢,
  convert hk using 3,
  rw [mul_add, mul_comm ↑a, ← mul_assoc _ ↑b, mul_comm _ ↑b, mul_assoc ↑b],
  congr' 2,
  { rw [← subtype.coe_inj],
    simp only [fin.coe_mk, subsemiring_class.coe_pow, _root_.coe_zpow', coe_coe,
      is_primitive_root.coe_unit'_coe],
    refine eq_of_div_eq_one _,
    rw [← zpow_coe_nat, ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd],
    simp [nat_abs_of_nonneg (mod_nonneg _ hpcoe), ← zmod.int_coe_zmod_eq_zero_iff_dvd] },
  { rw [← subtype.coe_inj],
    simp only [fin.coe_mk, subsemiring_class.coe_pow, mul_mem_class.coe_mul, _root_.coe_zpow',
      coe_coe, is_primitive_root.coe_unit'_coe, is_primitive_root.coe_inv_unit'_coe],
    refine eq_of_div_eq_one _,
    rw [← zpow_coe_nat, ← zpow_sub_one₀ (hζ'.ne_zero hpri.out.ne_zero),
      ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd, pnat.mk_coe],
    simp [nat_abs_of_nonneg (mod_nonneg _ hpcoe), ← zmod.int_coe_zmod_eq_zero_iff_dvd] },
end

/-- Auxiliary function -/
def f (a b : ℤ) (k₁ k₂ : ℕ) : ℕ → ℤ := λ x, if x = 0 then a else if x = 1 then b else
  if x = k₁ then -a else if x = k₂ then -b else 0

lemma auxf' (hp5 : 5 ≤ p) (a b : ℤ) (k₁ k₂ : fin p) : ∃ i ∈ range p, f a b k₁ k₂ (i : ℕ) = 0 :=
begin
  have h0 : 0 < p := by linarith,
  have h1 : 1 < p := by linarith,
  let s := ({0, 1, k₁, k₂} : finset ℕ),
  have : s.card ≤ 4,
  { repeat { refine le_trans (card_insert_le _ _) (succ_le_succ _) },
    exact rfl.ge },
  replace this : s.card < 5 := lt_of_le_of_lt this (by norm_num),
  have hs : s ⊆ range p := insert_subset.2 ⟨mem_range.2 h0, insert_subset.2 ⟨mem_range.2 h1,
    insert_subset.2 ⟨mem_range.2 (fin.is_lt _), singleton_subset_iff.2 (mem_range.2 (fin.is_lt _))⟩⟩⟩,
  have hcard := card_sdiff hs,
  replace hcard : (range p \ s).nonempty,
  { rw [← card_pos, hcard, card_range],
    exact nat.sub_pos_of_lt (lt_of_lt_of_le this hp5) },
  obtain ⟨i, hi⟩ := hcard,
  refine ⟨i, sdiff_subset _ _ hi, _⟩,
  have hi0 : i ≠ 0 := λ h, by simpa [h] using hi,
  have hi1 : i ≠ 1 := λ h, by simpa [h] using hi,
  have hik₁ : i ≠ k₁ := λ h, by simpa [h] using hi,
  have hik₂ : i ≠ k₂ := λ h, by simpa [h] using hi,
  simp [f, hi0, hi1, hik₁, hik₂]
end

lemma auxf (hp5 : 5 ≤ p) (a b : ℤ) (k₁ k₂ : fin p) : ∃ i : fin p, f a b k₁ k₂ (i : ℕ) = 0 :=
begin
  obtain ⟨i, hrange, hi⟩ := auxf' hp5 a b k₁ k₂,
  exact ⟨⟨i, mem_range.1 hrange⟩, hi⟩
end

local attribute [-instance] cyclotomic_field.algebra

/-- Case I with additional assumptions. -/
theorem caseI_easier {a b c : ℤ} (p : ℕ) [hpri : fact p.prime]
  (hreg : is_regular_prime p) (hp5 : 5 ≤ p)
  (hgcd : ({a, b, c} : finset ℤ).gcd id = 1)
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
begin
  haveI := (⟨hpri.out⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },
  set ζ := zeta P ℤ R with hζdef,
  have hζ := zeta_spec P ℤ R,

  intro H,
  obtain ⟨k₁, k₂, hcong, hdiv⟩ := ex_fin_div hp5 hreg hζ hgcd caseI H,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f a b k₁ k₂ j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    have h01 : 0 ≠ 1 := zero_ne_one,
    have h0k₁ : 0 ≠ ↑k₁ := aux0k₁ hpri.out hp5 hζ caseI hcong hdiv,
    have h0k₂ : 0 ≠ ↑k₂ := aux0k₂ hpri.out hp5 hζ hab hcong hdiv,
    have h1k₁ : 1 ≠ ↑k₁ := aux1k₁ hpri.out hp5 hζ hab hcong hdiv,
    have h1k₂ : 1 ≠ ↑k₂ := aux1k₂ hpri.out hp5 hζ caseI hcong hdiv,
    have hk₁k₂ : (k₁ : ℕ) ≠ (k₂ : ℕ) := auxk₁k₂ hpri.out hcong,
    simp_rw [f, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right h01,
      and_assoc, ne_and_eq_iff_right h1k₁, ne_and_eq_iff_right h0k₁, ne_and_eq_iff_right hk₁k₂,
      ne_and_eq_iff_right h1k₂, ne_and_eq_iff_right h0k₂, finset.range_filter_eq],
    simp only [hpri.out.pos, hpri.out.one_lt, if_true, zsmul_eq_mul, sum_singleton, pow_zero,
      mul_one, pow_one, fin.is_lt, neg_smul, sum_neg_distrib, ne.def, filter_congr_decidable, zero_smul, sum_const_zero, add_zero],
    ring },
  rw [sum_range] at key,
  refine caseI (has_dvd.dvd.mul_right (has_dvd.dvd.mul_right _ _) _),
  simpa [f] using dvd_coeff_cycl_integer hζ (by exact auxf hp5 a b k₁ k₂) key ⟨0, hpri.out.pos⟩
end

/-- CaseI. -/
theorem caseI {a b c : ℤ} {p : ℕ} [fact p.prime] (hreg : is_regular_prime p)
  (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
flt_regular.caseI.may_assume (λ x y z p₁ Hpri Hreg Hp5 Hunit Hxy HI H,
  by exactI caseI_easier p₁ Hreg Hp5 Hunit Hxy HI H) hreg caseI

end flt_regular
