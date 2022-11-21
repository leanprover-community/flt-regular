import may_assume.lemmas
import number_theory.cyclotomic.factoring
import number_theory.cyclotomic.Unit_lemmas
import ready_for_mathlib.exists_eq_pow_of_mul_eq_pow
import ready_for_mathlib.roots_of_unity
import number_theory.cyclotomic.case_I
import ready_for_mathlib.finset
import ready_for_mathlib.logic

open finset nat is_cyclotomic_extension ideal polynomial int basis

open_locale big_operators number_field

local attribute [-instance] cyclotomic_field.algebra

namespace flt_regular

variables {p : ℕ} (hpri : p.prime)

local notation `P` := (⟨p, hpri.pos⟩ : ℕ+)
local notation `K` := cyclotomic_field P ℚ
local notation `R` := 𝓞 K

namespace caseI

lemma two_lt (hp5 : 5 ≤ p) : 2 < p := by linarith

section zerok₁

lemma aux_cong0k₁ {k : fin p} (hcong : k ≡ -1 [ZMOD p]) : k = ⟨p.pred, pred_lt hpri.ne_zero⟩ :=
begin
  refine fin.ext _,
  rw [fin.coe_mk, ← zmod.val_cast_of_lt (fin.is_lt k)],
  suffices : ((k : ℤ) : zmod p).val = p.pred, simpa,
  rw [← zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [hcong, cast_neg, int.cast_one, pred_eq_sub_one],
  haveI : ne_zero p := ⟨hpri.ne_zero⟩,
  haveI : fact (p.prime) := ⟨hpri⟩,
  haveI : fact (1 < p) := ⟨hpri.one_lt⟩,
  simp [zmod.neg_val, zmod.val_one]
end

/-- Auxiliary function. -/
def f0k₁ (b : ℤ) (p : ℕ) : ℕ → ℤ := λ x, if x = 1 then b else if x = p.pred then -b else 0

lemma auxf0k₁ (hp5 : 5 ≤ p) (b : ℤ) : ∃ i : fin P, f0k₁ b p (i : ℕ) = 0 :=
begin
  refine ⟨⟨2, two_lt hp5⟩, _⟩,
  have h1 : ((⟨2, two_lt hp5⟩ : fin p) : ℕ) ≠ 1,
  { intro h,
    simp only [fin.ext_iff, fin.coe_mk] at h,
    exact one_lt_two.ne h.symm },
  have hpred : ((⟨2, two_lt hp5⟩ : fin p) : ℕ) ≠ p.pred,
  { intro h,
    simp only [fin.ext_iff, fin.coe_mk] at h,
    replace h := h.symm,
    rw [nat.pred_eq_succ_iff] at h,
    linarith },
  simp only [f0k₁, h1, if_false, hpred]
end

lemma aux0k₁ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (caseI : ¬ ↑p ∣ a * b * c) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 0 ≠ ↑k₁ :=
begin
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },

  symmetry,
  intro habs,
  rw [show (k₁ : ℤ) = 0, by simpa using habs, zero_sub] at hcong,
  rw [habs, pow_zero, mul_one, add_sub_cancel', aux_cong0k₁ hpri hcong] at hdiv,
  nth_rewrite 0 [show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : fin p) : ℕ), by simp] at hdiv,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f0k₁ b p j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    have h : 1 ≠ p.pred := λ h, by linarith [pred_eq_succ_iff.1 h.symm],
    simp_rw [f0k₁, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right h,
      finset.range_filter_eq],
    simp [hpri.one_lt, pred_lt (hpri.ne_zero), sub_eq_add_neg] },
  rw [sum_range] at key,
  refine caseI (has_dvd.dvd.mul_right (has_dvd.dvd.mul_left _ _) _),
  simpa [f0k₁] using dvd_coeff_cycl_integer (by exact hζ) (auxf0k₁ hpri hp5 b) key ⟨1, hpri.one_lt⟩,
end

end zerok₁

section zerok₂

/-- Auxiliary function -/
def f0k₂ (a b : ℤ) : ℕ → ℤ := λ x, if x = 0 then a - b else if x = 1 then b - a else 0

lemma aux_cong0k₂ {k : fin p} (hcong : k ≡ 1 [ZMOD p]) : k = ⟨1, hpri.one_lt⟩ :=
begin
  refine fin.ext _,
  rw [fin.coe_mk, ← zmod.val_cast_of_lt (fin.is_lt k)],
  suffices : ((k : ℤ) : zmod p).val = 1, simpa,
  rw [← zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [hcong, int.cast_one],
  haveI : fact (p.prime) := ⟨hpri⟩,
  simp [zmod.val_one]
end

lemma auxf0k₂ (hp5 : 5 ≤ p) (a b : ℤ) : ∃ i : fin P, f0k₂ a b (i : ℕ) = 0 :=
begin
  refine ⟨⟨2, two_lt hp5⟩, _⟩,
  have h1 : ((⟨2, two_lt hp5⟩ : fin p) : ℕ) ≠ 1,
  { intro h,
    simp only [fin.ext_iff, fin.coe_mk] at h,
    exact one_lt_two.ne h.symm },
  have hzero : ((⟨2, two_lt hp5⟩ : fin p) : ℕ) ≠ 0,
  { intro h,
    simp only [fin.ext_iff, fin.coe_mk] at h,
    linarith },
  simp only [f0k₂, h1, if_false, hzero]
end

lemma aux0k₂ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (hab : ¬a ≡ b [ZMOD p]) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 0 ≠ ↑k₂ :=
begin
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },

  symmetry,
  intro habs,
  replace hcong := hcong.symm,
  rw [show (k₂ : ℤ) = 0, by simpa using habs, ← zmod.int_coe_eq_int_coe_iff,
    int.cast_sub, int.cast_zero, sub_eq_zero, zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [habs, pow_zero, mul_one, aux_cong0k₂ hpri hcong, fin.coe_mk, pow_one, add_sub_assoc,
    ← sub_mul, add_sub_right_comm, show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : fin p) : ℕ), by simp,
    ← neg_sub ↑a, neg_mul, ← sub_eq_add_neg] at hdiv,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f0k₂ a b j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    simp_rw [f0k₂, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right zero_ne_one,
      finset.range_filter_eq],
    simp only [hpri.pos, hpri.one_lt, if_true, zsmul_eq_mul, int.cast_sub, sum_singleton, pow_zero,
      mul_one, pow_one, ne.def, filter_congr_decidable, zero_smul, sum_const_zero, add_zero,
      fin.coe_mk],
    ring },
  rw [sum_range] at key,
  refine hab _,
  symmetry,
  rw [← zmod.int_coe_eq_int_coe_iff, zmod.int_coe_eq_int_coe_iff_dvd_sub],
  simpa [f0k₂] using dvd_coeff_cycl_integer (by exact hζ) (auxf0k₂ hpri hp5 a b) key ⟨0, hpri.pos⟩
end

end zerok₂

section onek_one

lemma aux_cong1k₁ {k : fin p} (hcong : k ≡ 0 [ZMOD p]) : k = ⟨0, hpri.pos⟩ :=
begin
  refine fin.ext _,
  rw [fin.coe_mk, ← zmod.val_cast_of_lt (fin.is_lt k)],
  suffices : ((k : ℤ) : zmod p).val = 0, simpa,
  rw [← zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [hcong, int.cast_zero],
  haveI : fact (p.prime) := ⟨hpri⟩,
  simp
end

lemma aux1k₁ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (hab : ¬a ≡ b [ZMOD p]) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 1 ≠ ↑k₁ :=
begin
  intro habs,
  have h := aux0k₂ hpri hp5 hζ hab hcong hdiv,
  rw [show (k₁ : ℤ) = 1, by simpa using habs.symm, sub_self] at hcong,
  have := (aux_cong1k₁ hpri hcong),
  simp only [←fin.coe_eq_coe, fin.coe_mk] at this,
  exact h.symm this
end

end onek_one

section onek_two

/-- Auxiliary function -/
def f1k₂ (a : ℤ) : ℕ → ℤ := λ x, if x = 0 then a else if x = 2 then -a else 0

lemma aux_cong1k₂ {k : fin p} (hpri : p.prime) (hp5 : 5 ≤ p) (hcong : k ≡ 1 + 1 [ZMOD p]) :
  k = ⟨2, two_lt hp5⟩ :=
begin
  refine fin.ext _,
  rw [fin.coe_mk, ← zmod.val_cast_of_lt (fin.is_lt k)],
  suffices : ((k : ℤ) : zmod p).val = 2, simpa,
  rw [← zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [hcong],
  simp only [int.cast_add, algebra_map.coe_one],
  haveI : fact (p.prime) := ⟨hpri⟩,
  have := congr_arg nat.succ (nat.succ_pred_eq_of_pos hpri.pred_pos),
  rw [succ_pred_prime hpri] at this,
  rw [zmod.val_add, zmod.val_one, ← nat.mod_add_mod, ← this, one_mod, this, nat.mod_eq_of_lt],
  linarith
end

lemma auxf1k₂ (a : ℤ) : ∃ i : fin P, f1k₂ a (i : ℕ) = 0 :=
begin
  refine ⟨⟨1, hpri.one_lt⟩, _⟩,
  have h2 : ((⟨1, hpri.one_lt⟩ : fin p) : ℕ) ≠ 2,
  { intro h,
    simp only [fin.ext_iff, fin.coe_mk] at h,
    linarith },
  have hzero : ((⟨1, hpri.one_lt⟩ : fin p) : ℕ) ≠ 0,
  { intro h,
    simp only [fin.ext_iff, fin.coe_mk] at h,
    linarith },
  simp only [f1k₂, h2, if_false, hzero]
end

lemma aux1k₂ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (caseI : ¬ ↑p ∣ a * b * c) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 1 ≠ ↑k₂ :=
begin
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },

  symmetry,
  intro habs,
  replace hcong := hcong.symm,
  rw [show (k₂ : ℤ) = 1, by simpa using habs, ← zmod.int_coe_eq_int_coe_iff, int.cast_sub,
    sub_eq_iff_eq_add, ← int.cast_add, zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [habs, pow_one, (aux_cong1k₂ hpri hp5 hcong)] at hdiv,
  ring_nf at hdiv,
  rw [add_mul, one_mul, add_comm, mul_comm, mul_neg] at hdiv,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f1k₂ a j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    simp_rw [f1k₂, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right
      (show 0 ≠ 2, by norm_num), finset.range_filter_eq],
    simp [hpri.pos, two_lt hp5, fin.coe_mk (two_lt hp5),eq_self_iff_true, -fin.mk_bit0] },
  rw [sum_range] at key,
  refine caseI (has_dvd.dvd.mul_right (has_dvd.dvd.mul_right _ _) _),
  simpa [f1k₂] using dvd_coeff_cycl_integer (by exact hζ) (auxf1k₂ hpri a) key ⟨0, hpri.pos⟩
end

end onek_two

section kone_ktwo

lemma auxk₁k₂ {k₁ k₂ : fin p} (hpri : p.prime) (hcong : k₂ ≡ k₁ - 1 [ZMOD p]) : (k₁ : ℕ) ≠ (k₂ : ℕ) :=
begin
  haveI := (⟨hpri⟩ : fact (p.prime)),
  intro habs,
  rw [show (k₁ : ℤ) = (k₂ : ℕ), by simpa using habs, ← zmod.int_coe_eq_int_coe_iff, ← sub_eq_zero,
    int.cast_sub, sub_sub_eq_add_sub, coe_coe, add_sub_cancel', algebra_map.coe_one] at hcong,
  exact one_ne_zero hcong
end

end kone_ktwo

end caseI

end flt_regular
