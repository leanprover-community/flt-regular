module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Lower bounds for multiplicative orders

This file gives a criterion for bounding the order of a unit in `ZMod` from below.
-/

@[expose] public section

/-- If no positive power through `n` is `1` modulo `b`, then the multiplicative order exceeds
`n`. -/
lemma orderOf_lt_of {a b n : ℕ} [hn : Fact (b.Prime)] (h : a.Coprime b)
    (H : ∀ i ≤ n, 1 ≤ i → a ^ i % b ≠ 1) :
    n < orderOf (ZMod.unitOfCoprime _ h) := by
  by_contra! Habs
  refine H _ Habs (Nat.one_le_iff_ne_zero.mpr (orderOf_pos (ZMod.unitOfCoprime a h)).ne') ?_
  have : Fact (1 < b) := ⟨hn.1.one_lt⟩
  have := pow_orderOf_eq_one (ZMod.unitOfCoprime _ h)
  apply_fun Units.val at this
  simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at this
  simp [← ZMod.val_natCast, Nat.cast_pow, this, ZMod.val_one]
