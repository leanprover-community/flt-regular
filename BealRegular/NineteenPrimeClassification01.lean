import BealRegular.NineteenBoundsData
import Mathlib.Tactic.IntervalCases

/-! Exhaustive p = 19 split-prime classification for k in [125, 249]. -/

set_option maxHeartbeats 0 in
-- Checks every candidate in this bounded interval by explicit arithmetic cases.
set_option maxRecDepth 20000 in
theorem prime_mem_exceptionalSplitPrimesNineteen_01 :
    ∀ k ∈ Finset.Icc 125 249, (19 * k + 1).Prime →
      19 * k + 1 ∈ exceptionalSplitPrimesNineteen_00 := by
  intro k hk hp
  simp only [Finset.mem_Icc] at hk
  obtain ⟨hk125, hk249⟩ := hk
  interval_cases k
  all_goals solve
    | norm_num at hp
    | norm_num [exceptionalSplitPrimesNineteen_00]
