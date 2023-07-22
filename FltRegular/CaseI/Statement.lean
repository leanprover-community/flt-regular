import FltRegular.CaseI.AuxLemmas

open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI

open scoped BigOperators NumberField

namespace FltRegular

variable {p : ℕ} [hpri : Fact p.Prime]

set_option quotPrecheck false
local notation "P" => (⟨p, hpri.out.pos⟩ : ℕ+)

local notation "K" => CyclotomicField P ℚ

local notation "R" => 𝓞 K

namespace CaseI

/-- Statement of case I with additional assumptions. -/
def SlightlyEasier : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [hpri : Fact p.Prime] (_ : @IsRegularPrime p hpri) (_ : 5 ≤ p)
    (_ : ({a, b, c} : Finset ℤ).gcd id = 1) (_ : ¬a ≡ b [ZMOD p]) (_ : ¬↑p ∣ a * b * c),
    a ^ p + b ^ p ≠ c ^ p

/-- Statement of case I. -/
def Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [hpri : Fact p.Prime] (_ : @IsRegularPrime p hpri)
    (_ : ¬↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

theorem may_assume : SlightlyEasier → Statement := by
  intro Heasy
  intro a b c p hpri hreg hI H
  have hodd : p ≠ 2 := by
    intro h
    rw [h] at H hI
    refine' hI _
    refine' Dvd.dvd.mul_left _ _
    simp only [Nat.cast_ofNat] at hI ⊢
    rw [← even_iff_two_dvd, ← Int.odd_iff_not_even] at hI
    rw [← even_iff_two_dvd, ← Int.even_pow' (show 2 ≠ 0 by norm_num), ← H]
    exact (Int.Odd.of_mul_left (Odd.of_mul_left hI)).pow.add_odd
      (Int.Odd.of_mul_right (Odd.of_mul_left hI)).pow
  have hprod : a * b * c ≠ 0 := by
    intro h
    simp [h] at hI
  have hp5 : 5 ≤ p := by
    by_contra' habs
    have : p ∈ Finset.Ioo 2 5 :=
     (Finset.mem_Ioo).2 ⟨Nat.lt_of_le_and_ne hpri.out.two_le hodd.symm, by linarith⟩
    fin_cases this
    · exact MayAssume.p_ne_three hprod H rfl
    · rw [show 2 + 1 + 1 = 2 * 2 from rfl] at hpri
      refine' Nat.not_prime_mul one_lt_two one_lt_two hpri.out
  rcases MayAssume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩
  let d := ({a, b, c} : Finset ℤ).gcd id
  have hdiv : ¬↑p ∣ a / d * (b / d) * (c / d) :=
    by
    have hadiv : d ∣ a := gcd_dvd (by simp)
    have hbdiv : d ∣ b := gcd_dvd (by simp)
    have hcdiv : d ∣ c := gcd_dvd (by simp)
    intro hdiv
    replace hdiv := dvd_mul_of_dvd_right hdiv (d * d * d)
    rw [mul_assoc, ← mul_assoc d, ← mul_assoc d, Int.mul_ediv_cancel' hadiv, mul_assoc, mul_comm a,
      mul_assoc (b / d), ← mul_assoc _ (b / d), Int.mul_ediv_cancel' hbdiv, mul_comm, mul_assoc,
      mul_assoc, Int.ediv_mul_cancel hcdiv, mul_comm, mul_assoc, mul_comm c, ← mul_assoc] at hdiv
    exact hI hdiv
  obtain ⟨X, Y, Z, H1, H2, H3, _, H5⟩ := a_not_cong_b hpri.out hp5 hprodxyx Hxyz hunit hdiv
  exact Heasy hreg hp5 H2 H3 (fun hfin => H5 hfin) H1

end CaseI

theorem ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) : IsCoprime a b := by
  rw [← gcd_eq_one_iff_coprime]
  by_contra' h
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h
  replace hqpri : Prime (q : ℤ) := prime_iff_natAbs_prime.2 (by simp [hqpri])
  obtain ⟨n, hn⟩ := hq
  have haq : ↑q ∣ a := by
    obtain ⟨m, hm⟩ := Int.gcd_dvd_left a b
    exact ⟨n * m, by rw [hm, hn]; simp [mul_assoc]⟩
  have hbq : ↑q ∣ b := by
    obtain ⟨m, hm⟩ := Int.gcd_dvd_right a b
    exact ⟨n * m, by rw [hm, hn]; simp [mul_assoc]⟩
  have hcq : ↑q ∣ c := by
    suffices ↑q ∣ c ^ p by exact hqpri.dvd_of_dvd_pow this
    rw [← H]
    exact dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero)
  have Hq : ↑q ∣ ({a, b, c} : Finset ℤ).gcd id := by
    refine' dvd_gcd fun x hx => _
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with (H | H | H) <;> simpa [H]
  rw [hgcd] at Hq
  exact hqpri.not_unit (isUnit_of_dvd_one Hq)

theorem exists_ideal {a b c : ℤ} (h5p : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c) {ζ : R}
    (hζ : ζ ∈ nthRootsFinset p R) : ∃ I, span ({a + ζ * b} : Set R) = I ^ p :=
  by
  haveI : Fact (P : ℕ).Prime := ⟨hpri.out⟩
  classical
  have H₁ := congr_arg (algebraMap ℤ R) H
  simp only [eq_intCast, Int.cast_add, Int.cast_pow] at H₁
  have hζ' := (zeta_spec P ℚ K).unit'_coe
  rw [pow_add_pow_eq_prod_add_zeta_runity_mul
      (hpri.out.eq_two_or_odd.resolve_left fun h => by norm_num [h] at h5p ) hζ'] at H₁
  replace H₁ := congr_arg (fun x => span ({x} : Set R)) H₁
  simp only [← prod_span_singleton, ← span_singleton_pow] at H₁
  have hdom : IsDomain (Ideal (𝓞 (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ))) := Ideal.isDomain
  let gcddom : GCDMonoid (Ideal (𝓞 (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ))) :=
    Ideal.normalizedGcdMonoid.toGcdMonoid
  obtain ⟨I, hI⟩ :=
    @Finset.exists_eq_pow_of_mul_eq_pow_of_coprime _ _ _ hdom gcddom _ _ _ _ _
      (fun η₁ hη₁ η₂ hη₂ hη => _) H₁ ζ hζ
  · exact ⟨I, hI⟩
  · exact fltIdeals_coprime h5p H (ab_coprime H hpri.out.ne_zero hgcd) hη₁ hη₂ hη caseI

theorem is_principal {a b c : ℤ} {ζ : R} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c) (H : a ^ p + b ^ p = c ^ p)
    (hζ : IsPrimitiveRoot ζ p) : ∃ (u : Rˣ) (α : R), ↑u * α ^ p = ↑a + ζ * ↑b := by
  replace hζ := hζ.mem_nth_roots_finset hpri.out.pos
  obtain ⟨I, hI⟩ := exists_ideal hp5 H hgcd caseI hζ
  by_cases hIpzero : I ^ p = 0
  · refine' ⟨1, 0, _⟩
    simp [hIpzero, zero_eq_bot, span_singleton_eq_bot] at hI
    simp [hpri.out.pos, hI]
  have hIzero : I ≠ 0 := by
    intro hIzero
    simp only [hIzero, zero_pow hpri.out.pos] at hIpzero
    exact hIpzero rfl
  have hIprin : I.is_principal :=
    by
    have : ClassGroup.mk0 ⟨_, mem_nonZeroDivisors_of_ne_zero hIpzero⟩ = 1 :=
      by
      rw [ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero hIpzero)]
      exact ⟨⟨↑a + ζ * ↑b, hI.symm⟩⟩
    rw [← SubmonoidClass.mk_pow I (mem_nonZeroDivisors_of_ne_zero hIzero), map_pow] at this
    cases' (dvd_prime hpri.out).1 (orderOf_dvd_of_pow_eq_one this) with h1 habs
    · exact (ClassGroup.mk0_eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
    · exfalso
      refine' hpri.out.coprime_iff_not_dvd.1 hreg _
      simp_rw [← habs]
      exact orderOf_dvd_card_univ
  obtain ⟨α, hα⟩ := hIprin
  replace hα := congr_arg (fun J => J ^ p) hα
  simp only [← hI, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hα
  obtain ⟨u, hu⟩ := hα
  refine' ⟨u⁻¹, α, _⟩
  rw [← hu, mul_comm _ ↑u, ← mul_assoc]
  simp only [Units.inv_mul, one_mul]

theorem ex_fin_div {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hreg : IsRegularPrime p)
    (hζ : IsPrimitiveRoot ζ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c)
    (H : a ^ p + b ^ p = c ^ p) :
    ∃ k₁ k₂ : Fin p,
      k₂ ≡ k₁ - 1 [ZMOD p] ∧ ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  let ζ' := (ζ : K)
  have hζ' : IsPrimitiveRoot ζ' P := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  have : ζ = (hζ'.unit' : R) := by simp only [IsPrimitiveRoot.unit', SetLike.eta, Units.val_mk]
  have hP : P ≠ 2 := by
    intro hP
    rw [← PNat.coe_inj, PNat.mk_coe, PNat.coe_bit0, PNat.one_coe] at hP
    norm_num [hP] at hp5
  haveI := (⟨hpri.out⟩ : Fact (P : ℕ).Prime)
  obtain ⟨u, α, hu⟩ := is_principal hreg hp5 hgcd caseI H hζ
  rw [this, mul_comm _ ↑b, ← pow_one hζ'.unit'] at hu
  obtain ⟨k, hk⟩ := FltRegular.CaseI.exists_int_sum_eq_zero hζ' hP a b 1 hu.symm
  simp only [zpow_one, zpow_neg, coe_coe, PNat.mk_coe, mem_span_singleton, ← this] at hk
  have hpcoe : (p : ℤ) ≠ 0 := by simp [hpri.out.ne_zero]
  refine' ⟨⟨(2 * k % p).natAbs, _⟩, ⟨((2 * k - 1) % p).natAbs, _⟩, _, _⟩
  repeat'
    rw [← nat_abs_of_nat p]
    refine' nat_abs_lt_nat_abs_of_nonneg_of_lt (mod_nonneg _ hpcoe) _
    rw [nat_abs_of_nat]
    exact mod_lt_of_pos _ (by simp [hpri.out.pos])
  · simp [nat_abs_of_nonneg (mod_nonneg _ hpcoe), ← ZMod.int_cast_eq_int_cast_iff]
  simp only [add_sub_assoc, sub_sub] at hk ⊢
  convert hk using 3
  rw [mul_add, mul_comm ↑a, ← mul_assoc _ ↑b, mul_comm _ ↑b, mul_assoc ↑b]
  congr 2
  · rw [← Subtype.coe_inj]
    simp only [Fin.val_mk, SubsemiringClass.coe_pow, _root_.coe_zpow', coe_coe,
      IsPrimitiveRoot.coe_unit'_coe]
    refine' eq_of_div_eq_one _
    rw [← zpow_ofNat, ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp [nat_abs_of_nonneg (mod_nonneg _ hpcoe), ← ZMod.int_cast_zmod_eq_zero_iff_dvd]
  · rw [← Subtype.coe_inj]
    simp only [Fin.val_mk, SubsemiringClass.coe_pow, MulMemClass.coe_mul, _root_.coe_zpow', coe_coe,
      IsPrimitiveRoot.coe_unit'_coe, IsPrimitiveRoot.coe_inv_unit'_coe]
    refine' eq_of_div_eq_one _
    rw [← zpow_ofNat, ← zpow_sub_one₀ (hζ'.ne_zero hpri.out.ne_zero), ←
      zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd, PNat.mk_coe]
    simp [nat_abs_of_nonneg (mod_nonneg _ hpcoe), ← ZMod.int_cast_zmod_eq_zero_iff_dvd]

/-- Auxiliary function -/
def f (a b : ℤ) (k₁ k₂ : ℕ) : ℕ → ℤ := fun x =>
  if x = 0 then a else if x = 1 then b else if x = k₁ then -a else if x = k₂ then -b else 0

theorem auxf' (hp5 : 5 ≤ p) (a b : ℤ) (k₁ k₂ : Fin p) :
    ∃ i ∈ range p, f a b k₁ k₂ (i : ℕ) = 0 := by
  have h0 : 0 < p := by linarith
  have h1 : 1 < p := by linarith
  let s := ({0, 1, k₁, k₂} : Finset ℕ)
  have : s.card ≤ 4 := by
    repeat' refine' le_trans (card_insert_le _ _) (succ_le_succ _)
    exact rfl.ge
  replace this : s.card < 5 := lt_of_le_of_lt this (by norm_num)
  have hs : s ⊆ range p :=
    insert_subset.2
      ⟨mem_range.2 h0,
        insert_subset.2
          ⟨mem_range.2 h1,
            insert_subset.2
              ⟨mem_range.2 (Fin.is_lt _), singleton_subset_iff.2 (mem_range.2 (Fin.is_lt _))⟩⟩⟩
  have hcard := card_sdiff hs
  replace hcard : (range p \ s).Nonempty
  · rw [← card_pos, hcard, card_range]
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le this hp5)
  obtain ⟨i, hi⟩ := hcard
  refine' ⟨i, sdiff_subset _ _ hi, _⟩
  have hi0 : i ≠ 0 := fun h => by simpa [h] using hi
  have hi1 : i ≠ 1 := fun h => by simpa [h] using hi
  have hik₁ : i ≠ k₁ := fun h => by simpa [h] using hi
  have hik₂ : i ≠ k₂ := fun h => by simpa [h] using hi
  simp [f, hi0, hi1, hik₁, hik₂]

theorem auxf (hp5 : 5 ≤ p) (a b : ℤ) (k₁ k₂ : Fin p) : ∃ i : Fin p, f a b k₁ k₂ (i : ℕ) = 0 :=
  by
  obtain ⟨i, hrange, hi⟩ := auxf' hp5 a b k₁ k₂
  exact ⟨⟨i, mem_range.1 hrange⟩, hi⟩

/-- Case I with additional assumptions. -/
theorem caseI_easier {a b c : ℤ} (p : ℕ) [hpri : Fact p.Prime] (hreg : IsRegularPrime p)
    (hp5 : 5 ≤ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hab : ¬a ≡ b [ZMOD p])
    (caseI : ¬↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  haveI := (⟨hpri.out⟩ : Fact (P : ℕ).Prime)
  set ζ := zeta P ℤ R with hζdef
  have hζ := zeta_spec P ℤ R
  intro H
  obtain ⟨k₁, k₂, hcong, hdiv⟩ := ex_fin_div hp5 hreg hζ hgcd caseI H
  have key : ↑(p : ℤ) ∣ ∑ j in range p, f a b k₁ k₂ j • ζ ^ j :=
    by
    convert hdiv using 1
    have h01 : 0 ≠ 1 := zero_ne_one
    have h0k₁ : 0 ≠ ↑k₁ := aux0k₁ hpri.out hp5 hζ caseI hcong hdiv
    have h0k₂ : 0 ≠ ↑k₂ := aux0k₂ hpri.out hp5 hζ hab hcong hdiv
    have h1k₁ : 1 ≠ ↑k₁ := aux1k₁ hpri.out hp5 hζ hab hcong hdiv
    have h1k₂ : 1 ≠ ↑k₂ := aux1k₂ hpri.out hp5 hζ caseI hcong hdiv
    have hk₁k₂ : (k₁ : ℕ) ≠ (k₂ : ℕ) := auxk₁k₂ hpri.out hcong
    simp_rw [f, ite_smul, sum_ite, filter_filter, ← Ne.def, ne_and_eq_iff_right h01, and_assoc',
      ne_and_eq_iff_right h1k₁, ne_and_eq_iff_right h0k₁, ne_and_eq_iff_right hk₁k₂,
      ne_and_eq_iff_right h1k₂, ne_and_eq_iff_right h0k₂, Finset.range_filter_eq]
    simp only [hpri.out.pos, hpri.out.one_lt, if_true, zsmul_eq_mul, sum_singleton, pow_zero,
      mul_one, pow_one, Fin.is_lt, neg_smul, sum_neg_distrib, Ne.def, filter_congr_decidable,
      zero_smul, sum_const_zero, add_zero]
    ring
  rw [sum_range] at key
  refine' caseI (Dvd.Dvd.mul_right (Dvd.Dvd.mul_right _ _) _)
  simpa [f] using dvd_coeff_cycl_integer hζ (auxf hp5 a b k₁ k₂) key ⟨0, hpri.out.pos⟩

/-- CaseI. -/
theorem caseI {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p)
    (caseI : ¬↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
  FltRegular.CaseI.may_assume
    (fun x y z p₁ Hpri Hreg Hp5 Hunit Hxy HI H => caseI_easier p₁ Hreg Hp5 Hunit Hxy HI H) hreg
    caseI

end FltRegular
