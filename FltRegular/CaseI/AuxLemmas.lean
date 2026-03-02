module

public import Mathlib.NumberTheory.Cyclotomic.Basic
import FltRegular.NumberTheory.Cyclotomic.CyclRat
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Nat.Factorial.DoubleFactorial

@[expose] public section

open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis

open scoped NumberField

namespace FltRegular

variable {p : ℕ} (hpri : p.Prime)

local notation "K" => CyclotomicField p ℚ

local notation "R" => 𝓞 K

namespace CaseI

theorem two_lt (hp5 : 5 ≤ p) : 2 < p := by linarith

section Zerok₁

theorem aux_cong0k₁ {k : Fin p} (hcong : k ≡ -1 [ZMOD p]) :
    k = ⟨p.pred, pred_lt hpri.ne_zero⟩ := by
  refine Fin.ext ?_
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices ((k : ℤ) : ZMod p).val = p.pred by simpa
  rw [← ZMod.intCast_eq_intCast_iff] at hcong
  rw [hcong, cast_neg, Int.cast_one, pred_eq_sub_one]
  haveI : NeZero p := ⟨hpri.ne_zero⟩
  haveI : Fact p.Prime := ⟨hpri⟩
  haveI : Fact (1 < p) := ⟨hpri.one_lt⟩
  simp [ZMod.neg_val, ZMod.val_one]

/-- Auxiliary function. -/
def f0k₁ (b : ℤ) (p : ℕ) : ℕ → ℤ := fun x => if x = 1 then b else if x = p.pred then -b else 0

theorem auxf0k₁ (hp5 : 5 ≤ p) (b : ℤ) : ∃ i : Fin p, f0k₁ b p (i : ℕ) = 0 := by
  refine ⟨⟨2, two_lt hp5⟩, ?_⟩
  have hpred : ((⟨2, two_lt hp5⟩ : Fin p) : ℕ) ≠ p.pred := by
    intro h
    simp only at h
    rw [Nat.pred_eq_sub_one] at h
    omega
  simp only [f0k₁, OfNat.ofNat_ne_one, ite_false, ite_eq_right_iff, neg_eq_zero]
  intro h2
  exfalso
  apply hpred
  simp [h2]

set_option backward.isDefEq.respectTransparency false in
include hpri in
theorem aux0k₁ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (caseI : ¬↑p ∣ a * b * c) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : 0 ≠ (k₁ : ℕ) := by
  symm
  intro habs
  rw [show (k₁ : ℤ) = 0 by simpa using habs, zero_sub] at hcong
  rw [habs, _root_.pow_zero, mul_one, add_sub_cancel_left, aux_cong0k₁ hpri hcong] at hdiv
  nth_rw 1 [show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) by simp] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f0k₁ b p j • ζ ^ j := by
    convert hdiv using 1
    have h : 1 ≠ p.pred := fun h => by linarith [pred_eq_succ_iff.1 h.symm]
    simp_rw [f0k₁, ite_smul, sum_ite, filter_filter, ← Ne.eq_def, ne_and_eq_iff_right h,
      Finset.range_filter_eq]
    simp [hpri.one_lt, Nat.sub_lt hpri.pos, sub_eq_add_neg]
  rw [sum_range] at key
  refine caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _)
  have : NeZero p := ⟨hpri.ne_zero⟩
  simpa [f0k₁] using dvd_coeff_cycl_integer hpri hζ (auxf0k₁ hp5 b) key ⟨1, hpri.one_lt⟩

end Zerok₁

section Zerok₂

/-- Auxiliary function -/
def f0k₂ (a b : ℤ) : ℕ → ℤ := fun x => if x = 0 then a - b else if x = 1 then b - a else 0

theorem aux_cong0k₂ {k : Fin p} (hcong : k ≡ 1 [ZMOD p]) : k = ⟨1, hpri.one_lt⟩ := by
  refine Fin.ext ?_
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices ((k : ℤ) : ZMod p).val = 1 by simpa
  rw [← ZMod.intCast_eq_intCast_iff] at hcong
  rw [hcong, Int.cast_one]
  haveI : Fact p.Prime := ⟨hpri⟩
  simp [ZMod.val_one]

theorem auxf0k₂ (hp5 : 5 ≤ p) (a b : ℤ) : ∃ i : Fin p, f0k₂ a b (i : ℕ) = 0 :=
  ⟨⟨2, two_lt hp5⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
include hpri in
theorem aux0k₂ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) (hab : ¬a ≡ b [ZMOD p])
    {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : (0 : ℕ) ≠ ↑k₂ := by
  symm
  intro habs
  replace hcong := hcong.symm
  rw [show (k₂ : ℤ) = 0 by simpa using habs, ← ZMod.intCast_eq_intCast_iff, Int.cast_sub,
    Int.cast_zero, sub_eq_zero, ZMod.intCast_eq_intCast_iff] at hcong
  rw [habs, _root_.pow_zero, mul_one, aux_cong0k₂ hpri hcong, Fin.val_mk, pow_one, add_sub_assoc,
    ← sub_mul, add_sub_right_comm, show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) by simp] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f0k₂ a b j • ζ ^ j := by
    convert hdiv using 1
    simp_rw [f0k₂, ite_smul, sum_ite, filter_filter, ← Ne.eq_def, ne_and_eq_iff_right zero_ne_one,
      Finset.range_filter_eq]
    simp only [hpri.pos, hpri.one_lt, if_true, zsmul_eq_mul, Int.cast_sub, sum_singleton,
      _root_.pow_zero, mul_one, pow_one, Ne, zero_smul, sum_const_zero, add_zero]
  rw [sum_range] at key
  refine hab ?_
  symm
  rw [← ZMod.intCast_eq_intCast_iff, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have : NeZero p := ⟨hpri.ne_zero⟩
  simpa [f0k₂] using dvd_coeff_cycl_integer hpri hζ (auxf0k₂ hp5 a b) key ⟨0, hpri.pos⟩

end Zerok₂

section OnekOne

theorem aux_cong1k₁ {k : Fin p} (hcong : k ≡ 0 [ZMOD p]) : k = ⟨0, hpri.pos⟩ := by
  refine Fin.ext ?_
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices ((k : ℤ) : ZMod p).val = 0 by simpa
  rw [← ZMod.intCast_eq_intCast_iff] at hcong
  rw [hcong, Int.cast_zero]
  haveI : Fact p.Prime := ⟨hpri⟩
  simp

include hpri in
theorem aux1k₁ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) (hab : ¬a ≡ b [ZMOD p])
    {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : (1 : ℕ) ≠ k₁ := by
  intro habs
  have h := aux0k₂ hpri hp5 hζ hab hcong hdiv
  rw [show (k₁ : ℤ) = 1 by simpa using habs.symm, sub_self] at hcong
  have := aux_cong1k₁ hpri hcong
  simp only [← Fin.val_eq_val] at this
  exact h.symm this

end OnekOne

section OnekTwo

/-- Auxiliary function -/
def f1k₂ (a : ℤ) : ℕ → ℤ := fun x => if x = 0 then a else if x = 2 then -a else 0

theorem aux_cong1k₂ {k : Fin p} (hpri : p.Prime) (hp5 : 5 ≤ p) (hcong : k ≡ 1 + 1 [ZMOD p]) :
    k = ⟨2, two_lt hp5⟩ := by
  refine Fin.ext ?_
  rw [Fin.val_mk, ← ZMod.val_cast_of_lt (Fin.is_lt k)]
  suffices ((k : ℤ) : ZMod p).val = 2 by simpa
  rw [← ZMod.intCast_eq_intCast_iff] at hcong
  rw [hcong]
  simp only [Int.cast_add]
  haveI : Fact p.Prime := ⟨hpri⟩
  have := congr_arg Nat.succ (Nat.succ_pred_eq_of_pos hpri.pred_pos)
  rw [succ_pred_prime hpri] at this
  rw [ZMod.val_add, Int.cast_one, ZMod.val_one, ← Nat.mod_add_mod, ← this, one_mod, this,
    Nat.mod_eq_of_lt]
  linarith

include hpri in
theorem auxf1k₂ (a : ℤ) : ∃ i : Fin p, f1k₂ a i = 0 :=
  ⟨⟨1, hpri.one_lt⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
include hpri in
theorem aux1k₂ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (caseI : ¬↑p ∣ a * b * c) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) : (1 : ℕ) ≠ k₂ := by
  symm
  intro habs
  replace hcong := hcong.symm
  rw [show (k₂ : ℤ) = 1 by simpa using habs, ← ZMod.intCast_eq_intCast_iff, Int.cast_sub,
    sub_eq_iff_eq_add, ← Int.cast_add, ZMod.intCast_eq_intCast_iff] at hcong
  rw [habs, pow_one, aux_cong1k₂ hpri hp5 hcong] at hdiv
  ring_nf at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f1k₂ a j • ζ ^ j := by
    suffices ∑ j ∈ range p, f1k₂ a j • ζ ^ j = ↑a - ↑a * ζ ^ 2 by
      rwa [this]
    simp_rw [f1k₂, ite_smul, sum_ite, filter_filter, ← Ne.eq_def, ne_and_eq_iff_right
      (show 0 ≠ 2 by norm_num), Finset.range_filter_eq]
    simp only [hpri.pos, ite_true, zsmul_eq_mul, sum_singleton, _root_.pow_zero, mul_one,
      two_lt hp5,neg_smul, sum_neg_distrib, ne_eq, zero_smul, sum_const_zero, add_zero]
    ring
  rw [sum_range] at key
  refine caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _)
  have : NeZero p := ⟨hpri.ne_zero⟩
  simpa [f1k₂] using dvd_coeff_cycl_integer hpri hζ (auxf1k₂ hpri a) key ⟨0, hpri.pos⟩

end OnekTwo

section KoneKtwo

theorem auxk₁k₂ {k₁ k₂ : Fin p} (hpri : p.Prime) (hcong : k₂ ≡ k₁ - 1 [ZMOD p]) :
    (k₁ : ℕ) ≠ (k₂ : ℕ) := by
  haveI := (⟨hpri⟩ : Fact p.Prime)
  intro habs
  rw [habs, ← ZMod.intCast_eq_intCast_iff, Int.cast_sub, ← sub_eq_zero] at hcong
  simp at hcong

end KoneKtwo

end CaseI

end FltRegular
