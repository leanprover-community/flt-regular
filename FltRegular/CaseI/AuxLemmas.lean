import FltRegular.MayAssume.Lemmas
import FltRegular.NumberTheory.Cyclotomic.Factoring
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.Cyclotomic.CaseI

open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis

open scoped BigOperators NumberField

namespace FltRegular

variable {p : ℕ} (hpri : p.Prime)

set_option quotPrecheck false
local notation "P" => (⟨p, hpri.pos⟩ : ℕ+)

local notation "K" => CyclotomicField P ℚ

local notation "R" => 𝓞 K

namespace CaseI

theorem two_lt (hp5 : 5 ≤ p) : 2 < p := by linarith

section Zerok₁

theorem aux_cong0k₁ {k : Fin p} (hcong : k ≡ -1 [ZMOD p]) :
  k = ⟨p.pred, pred_lt hpri.ne_zero⟩ := by
  refine' Fin.ext _
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices : ((k : ℤ) : ZMod p).val = p.pred; simpa
  rw [← ZMod.int_cast_eq_int_cast_iff] at hcong
  rw [hcong, cast_neg, Int.cast_one, pred_eq_sub_one]
  haveI : NeZero p := ⟨hpri.ne_zero⟩
  haveI : Fact p.Prime := ⟨hpri⟩
  haveI : Fact (1 < p) := ⟨hpri.one_lt⟩
  simp [ZMod.neg_val, ZMod.val_one]

/-- Auxiliary function. -/
def f0k₁ (b : ℤ) (p : ℕ) : ℕ → ℤ := fun x => if x = 1 then b else if x = p.pred then -b else 0

theorem auxf0k₁ (hp5 : 5 ≤ p) (b : ℤ) : ∃ i : Fin P, f0k₁ b p (i : ℕ) = 0 := by
  refine' ⟨⟨2, two_lt hp5⟩, _⟩
  have hpred : ((⟨2, two_lt hp5⟩ : Fin p) : ℕ) ≠ p.pred := by
    intro h
    simp only [Fin.ext_iff, Fin.val_mk] at h
    replace h := h.symm
    rw [Nat.pred_eq_succ_iff] at h
    linarith
  simp only [f0k₁, OfNat.ofNat_ne_one, ite_false, ite_eq_right_iff, neg_eq_zero]
  intro h2
  exfalso
  apply hpred
  simp [h2]

set_option pp.explicit true

theorem aux0k₁ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (caseI : ¬↑p ∣ a * b * c) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 0 ≠ (↑k₁ : ℕ) := by
  symm
  intro habs
  rw [show (k₁ : ℤ) = 0 by simpa using habs, zero_sub] at hcong
  rw [habs, _root_.pow_zero, mul_one, add_sub_cancel', aux_cong0k₁ hpri hcong] at hdiv
  nth_rw 1 [show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) by simp] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j in range p, f0k₁ b p j • ζ ^ j := by
    convert hdiv using 1
    have h : 1 ≠ p.pred := fun h => by linarith [pred_eq_succ_iff.1 h.symm]
    simp_rw [f0k₁, ite_smul, sum_ite, filter_filter, ← Ne.def, ne_and_eq_iff_right h,
      Finset.range_filter_eq]
    simp [hpri.one_lt, pred_lt hpri.ne_zero, sub_eq_add_neg]
  rw [sum_range] at key
  refine' caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_left _ _) _)
  simpa [f0k₁] using dvd_coeff_cycl_integer hpri hζ (auxf0k₁ hpri hp5 b) key ⟨1, hpri.one_lt⟩

end Zerok₁

section Zerok₂

/-- Auxiliary function -/
def f0k₂ (a b : ℤ) : ℕ → ℤ := fun x => if x = 0 then a - b else if x = 1 then b - a else 0

theorem aux_cong0k₂ {k : Fin p} (hcong : k ≡ 1 [ZMOD p]) : k = ⟨1, hpri.one_lt⟩ :=
  by
  refine' Fin.ext _
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices : ((k : ℤ) : ZMod p).val = 1; simpa
  rw [← ZMod.int_cast_eq_int_cast_iff] at hcong
  rw [hcong, Int.cast_one]
  haveI : Fact p.prime := ⟨hpri⟩
  simp [ZMod.val_one]

theorem auxf0k₂ (hp5 : 5 ≤ p) (a b : ℤ) : ∃ i : Fin P, f0k₂ a b (i : ℕ) = 0 :=
  by
  refine' ⟨⟨2, two_lt hp5⟩, _⟩
  have h1 : ((⟨2, two_lt hp5⟩ : Fin p) : ℕ) ≠ 1 :=
    by
    intro h
    simp only [Fin.ext_iff, Fin.val_mk] at h
    exact one_lt_two.ne h.symm
  have hzero : ((⟨2, two_lt hp5⟩ : Fin p) : ℕ) ≠ 0 :=
    by
    intro h
    simp only [Fin.ext_iff, Fin.val_mk] at h
    linarith
  simp only [f0k₂, h1, if_false, hzero]

theorem aux0k₂ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) (hab : ¬a ≡ b [ZMOD p])
    {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 0 ≠ ↑k₂ :=
  by
  haveI := (⟨hpri⟩ : Fact (P : ℕ).Prime)
  symm
  intro habs
  replace hcong := hcong.symm
  rw [show (k₂ : ℤ) = 0 by simpa using habs, ← ZMod.int_cast_eq_int_cast_iff, Int.cast_sub,
    Int.cast_zero, sub_eq_zero, ZMod.int_cast_eq_int_cast_iff] at hcong
  rw [habs, pow_zero, mul_one, aux_cong0k₂ hpri hcong, Fin.val_mk, pow_one, add_sub_assoc, ←
    sub_mul, add_sub_right_comm, show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) by simp, ←
    neg_sub ↑a, neg_mul, ← sub_eq_add_neg] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j in range p, f0k₂ a b j • ζ ^ j :=
    by
    convert hdiv using 1
    simp_rw [f0k₂, ite_smul, sum_ite, filter_filter, ← Ne.def, ne_and_eq_iff_right zero_ne_one,
      Finset.range_filter_eq]
    simp only [hpri.pos, hpri.one_lt, if_true, zsmul_eq_mul, Int.cast_sub, sum_singleton, pow_zero,
      mul_one, pow_one, Ne.def, filter_congr_decidable, zero_smul, sum_const_zero, add_zero,
      Fin.val_mk]
    ring
  rw [sum_range] at key
  refine' hab _
  symm
  rw [← ZMod.int_cast_eq_int_cast_iff, ZMod.int_cast_eq_int_cast_iff_dvd_sub]
  simpa [f0k₂] using dvd_coeff_cycl_integer hζ (auxf0k₂ hpri hp5 a b) key ⟨0, hpri.pos⟩

end Zerok₂

section OnekOne

theorem aux_cong1k₁ {k : Fin p} (hcong : k ≡ 0 [ZMOD p]) : k = ⟨0, hpri.Pos⟩ :=
  by
  refine' Fin.ext _
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices : ((k : ℤ) : ZMod p).val = 0; simpa
  rw [← ZMod.int_cast_eq_int_cast_iff] at hcong
  rw [hcong, Int.cast_zero]
  haveI : Fact p.prime := ⟨hpri⟩
  simp

theorem aux1k₁ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) (hab : ¬a ≡ b [ZMOD p])
    {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 1 ≠ ↑k₁ :=
  by
  intro habs
  have h := aux0k₂ hpri hp5 hζ hab hcong hdiv
  rw [show (k₁ : ℤ) = 1 by simpa using habs.symm, sub_self] at hcong
  have := aux_cong1k₁ hpri hcong
  simp only [← Fin.val_eq_val, Fin.val_mk] at this
  exact h.symm this

end OnekOne

section OnekTwo

/-- Auxiliary function -/
def f1k₂ (a : ℤ) : ℕ → ℤ := fun x => if x = 0 then a else if x = 2 then -a else 0

theorem aux_cong1k₂ {k : Fin p} (hpri : p.Prime) (hp5 : 5 ≤ p) (hcong : k ≡ 1 + 1 [ZMOD p]) :
    k = ⟨2, two_lt hp5⟩ := by
  refine' Fin.ext _
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices : ((k : ℤ) : ZMod p).val = 2; simpa
  rw [← ZMod.int_cast_eq_int_cast_iff] at hcong
  rw [hcong]
  simp only [Int.cast_add, algebraMap.coe_one]
  haveI : Fact p.prime := ⟨hpri⟩
  have := congr_arg Nat.succ (Nat.succ_pred_eq_of_pos hpri.pred_pos)
  rw [succ_pred_prime hpri] at this
  rw [ZMod.val_add, ZMod.val_one, ← Nat.mod_add_mod, ← this, one_mod, this, Nat.mod_eq_of_lt]
  linarith

theorem auxf1k₂ (a : ℤ) : ∃ i : Fin P, f1k₂ a (i : ℕ) = 0 :=
  by
  refine' ⟨⟨1, hpri.one_lt⟩, _⟩
  have h2 : ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) ≠ 2 :=
    by
    intro h
    simp only [Fin.ext_iff, Fin.val_mk] at h
    linarith
  have hzero : ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) ≠ 0 :=
    by
    intro h
    simp only [Fin.ext_iff, Fin.val_mk] at h
    linarith
  simp only [f1k₂, h2, if_false, hzero]

theorem aux1k₂ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (caseI : ¬↑p ∣ a * b * c) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 1 ≠ ↑k₂ :=
  by
  haveI := (⟨hpri⟩ : Fact (P : ℕ).Prime)
  symm
  intro habs
  replace hcong := hcong.symm
  rw [show (k₂ : ℤ) = 1 by simpa using habs, ← ZMod.int_cast_eq_int_cast_iff, Int.cast_sub,
    sub_eq_iff_eq_add, ← Int.cast_add, ZMod.int_cast_eq_int_cast_iff] at hcong
  rw [habs, pow_one, aux_cong1k₂ hpri hp5 hcong] at hdiv
  ring_nf at hdiv
  rw [add_mul, one_mul, add_comm, mul_comm, mul_neg] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j in range p, f1k₂ a j • ζ ^ j :=
    by
    convert hdiv using 1
    simp_rw [f1k₂, ite_smul, sum_ite, filter_filter, ← Ne.def,
      ne_and_eq_iff_right (show 0 ≠ 2 by norm_num), Finset.range_filter_eq]
    simp [hpri.pos, two_lt hp5, Fin.val_mk (two_lt hp5), eq_self_iff_true, -Fin.mk_bit0]
  rw [sum_range] at key
  refine' caseI (Dvd.Dvd.mul_right (Dvd.Dvd.mul_right _ _) _)
  simpa [f1k₂] using dvd_coeff_cycl_integer hζ (auxf1k₂ hpri a) key ⟨0, hpri.pos⟩

end OnekTwo

section KoneKtwo

theorem auxk₁k₂ {k₁ k₂ : Fin p} (hpri : p.Prime) (hcong : k₂ ≡ k₁ - 1 [ZMOD p]) :
    (k₁ : ℕ) ≠ (k₂ : ℕ) := by
  haveI := (⟨hpri⟩ : Fact p.prime)
  intro habs
  rw [show (k₁ : ℤ) = (k₂ : ℕ) by simpa using habs, ← ZMod.int_cast_eq_int_cast_iff, ← sub_eq_zero,
    Int.cast_sub, sub_sub_eq_add_sub, add_sub_cancel', algebraMap.coe_one] at hcong
  exact one_ne_zero hcong

end KoneKtwo

end CaseI

end FltRegular
