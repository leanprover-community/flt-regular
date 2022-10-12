import may_assume.lemmas
import number_theory.cyclotomic.factoring
import number_theory.cyclotomic.Unit_lemmas
import ready_for_mathlib.exists_eq_pow_of_mul_eq_pow
import ready_for_mathlib.roots_of_unity
import number_theory.cyclotomic.case_I

open finset nat is_cyclotomic_extension ideal polynomial int basis

open_locale big_operators number_field

local attribute [-instance] cyclotomic_field.algebra

section move_me

@[simp]
lemma finset.range_filter_eq {n m : ℕ} : (range n).filter (= m) = if m < n then {m} else ∅ :=
begin
  convert filter_eq (range n) m,
  { ext, exact comm },
  { simp }
end

lemma ne_and_eq_iff_right {α : Type*} {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
and_iff_right_of_imp (λ h2, h2.symm ▸ h.symm)

end move_me

namespace flt_regular

variables {p : ℕ} (hpri : p.prime)

local notation `P` := (⟨p, hpri.pos⟩ : ℕ+)
local notation `K` := cyclotomic_field P ℚ
local notation `R` := 𝓞 K

namespace caseI

lemma two_lt (hp5 : 5 ≤ p) : 2 < p := by linarith

section k_one_zero

lemma aux_cong₁₀ {k : fin p} (hcong : k ≡ -1 [ZMOD p]) : k = ⟨p.pred, pred_lt hpri.ne_zero⟩ :=
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
def f₁₀ (b : ℤ) (p : ℕ) : ℕ → ℤ := λ x, if x = 1 then b else if x = p.pred then -b else 0

lemma auxf₁₀ (hp5 : 5 ≤ p) (b : ℤ) : ∃ i : fin P, f₁₀ b p (i : ℕ) = 0 :=
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
  simp only [f₁₀, h1, if_false, hpred]
end

lemma aux₁₀ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (caseI : ¬ ↑p ∣ a * b * c) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : ↑k₁ ≠ 0 :=
begin
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },

  intro habs,
  rw [show (k₁ : ℤ) = 0, by simpa using habs, zero_sub] at hcong,
  rw [habs, pow_zero, mul_one, add_sub_cancel', aux_cong₁₀ hpri hcong] at hdiv,
  nth_rewrite 0 [show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : fin p) : ℕ), by simp] at hdiv,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f₁₀ b p j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    have h : 1 ≠ p.pred := λ h, by linarith [pred_eq_succ_iff.1 h.symm],
    simp_rw [f₁₀, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right h,
      finset.range_filter_eq],
    simp [hpri.one_lt, pred_lt (hpri.ne_zero), sub_eq_add_neg] },
  rw [sum_range] at key,
  refine caseI (has_dvd.dvd.mul_right (has_dvd.dvd.mul_left _ _) _),
  simpa [f₁₀] using dvd_coeff_cycl_integer (by exact hζ) (auxf₁₀ hpri hp5 b) key ⟨1, hpri.one_lt⟩,
end

end k_one_zero

section k_two_zero

/-- Auxiliary function -/
def f₂₀ (a b : ℤ) : ℕ → ℤ := λ x, if x = 0 then a - b else if x = 1 then b - a else 0

lemma aux_cong₂₀ {k : fin p} (hcong : k ≡ 1 [ZMOD p]) : k = ⟨1, hpri.one_lt⟩ :=
begin
  refine fin.ext _,
  rw [fin.coe_mk, ← zmod.val_cast_of_lt (fin.is_lt k)],
  suffices : ((k : ℤ) : zmod p).val = 1, simpa,
  rw [← zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [hcong, int.cast_one],
  haveI : fact (p.prime) := ⟨hpri⟩,
  simp [zmod.val_one]
end

lemma auxf₂₀ (hp5 : 5 ≤ p) (a b : ℤ) : ∃ i : fin P, f₂₀ a b (i : ℕ) = 0 :=
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
  simp only [f₂₀, h1, if_false, hzero]
end

lemma aux₂₀ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (hab : ¬a ≡ b [ZMOD p]) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : ↑k₂ ≠ 0 :=
begin
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },

  intro habs,
  replace hcong := hcong.symm,
  rw [show (k₂ : ℤ) = 0, by simpa using habs, ← zmod.int_coe_eq_int_coe_iff,
    int.cast_sub, int.cast_zero, sub_eq_zero, zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [habs, pow_zero, mul_one, aux_cong₂₀ hpri hcong, fin.coe_mk, pow_one, add_sub_assoc,
    ← sub_mul, add_sub_right_comm, show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : fin p) : ℕ), by simp,
    ← neg_sub ↑a, neg_mul, ← sub_eq_add_neg] at hdiv,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f₂₀ a b j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    simp_rw [f₂₀, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right zero_ne_one,
      finset.range_filter_eq],
    simp only [hpri.pos, hpri.one_lt, if_true, zsmul_eq_mul, int.cast_sub, sum_singleton, pow_zero,
      mul_one, pow_one, ne.def, filter_congr_decidable, zero_smul, sum_const_zero, add_zero,
      fin.coe_mk],
    ring },
  rw [sum_range] at key,
  refine hab _,
  symmetry,
  rw [← zmod.int_coe_eq_int_coe_iff, zmod.int_coe_eq_int_coe_iff_dvd_sub],
  simpa [f₂₀] using dvd_coeff_cycl_integer (by exact hζ) (auxf₂₀ hpri hp5 a b) key ⟨0, hpri.pos⟩
end

end k_two_zero

section k_two_one

/-- Auxiliary function -/
def f₂₁ (a : ℤ) : ℕ → ℤ := λ x, if x = 0 then a else if x = 2 then -a else 0

lemma aux_cong₂₁ {k : fin p} (hpri : p.prime) (hp5 : 5 ≤ p) (hcong : k ≡ 1 + 1 [ZMOD p]) :
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

lemma auxf₂₁ (a : ℤ) : ∃ i : fin P, f₂₁ a (i : ℕ) = 0 :=
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
  simp only [f₂₁, h2, if_false, hzero]
end

lemma aux₂₁ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : is_primitive_root ζ p)
  (caseI : ¬ ↑p ∣ a * b * c) {k₁ k₂ : fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
  (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : ↑k₂ ≠ 1 :=
begin
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K,
  { convert cyclotomic_field.is_cyclotomic_extension P ℚ,
    exact subsingleton.elim _ _ },

  intro habs,
  replace hcong := hcong.symm,
  rw [show (k₂ : ℤ) = 1, by simpa using habs, ← zmod.int_coe_eq_int_coe_iff, int.cast_sub,
    sub_eq_iff_eq_add, ← int.cast_add, zmod.int_coe_eq_int_coe_iff] at hcong,
  rw [habs, pow_one, (aux_cong₂₁ hpri hp5 hcong)] at hdiv,
  ring_nf at hdiv,
  rw [add_mul, one_mul, add_comm, mul_comm, mul_neg] at hdiv,
  have key : ↑(p : ℤ) ∣ ∑ j in range p, (f₂₁ a j) • ζ ^ j,
  { convert hdiv using 1,
    { simp },
    simp_rw [f₂₁, ite_smul, sum_ite, filter_filter, ← ne.def, ne_and_eq_iff_right
      (show 0 ≠ 2, by norm_num), finset.range_filter_eq],
    simp [hpri.pos, two_lt hp5, fin.coe_mk (two_lt hp5),eq_self_iff_true, -fin.mk_bit0] },
  rw [sum_range] at key,
  refine caseI (has_dvd.dvd.mul_right (has_dvd.dvd.mul_right _ _) _),
  simpa [f₂₁] using dvd_coeff_cycl_integer (by exact hζ) (auxf₂₁ hpri a) key ⟨0, hpri.pos⟩
end

end k_two_one

end caseI

end flt_regular
