import BealRegular.NineteenBoundsData
import Mathlib.Tactic.IntervalCases

/-! Exhaustive p = 19 split-prime classification for k in [1375, 1499]. -/

set_option maxHeartbeats 0 in
-- Checks every candidate in this bounded interval by explicit arithmetic cases.
set_option maxRecDepth 20000 in
theorem prime_mem_exceptionalSplitPrimesNineteen_11 :
    ∀ k ∈ Finset.Icc 1375 1499, (19 * k + 1).Prime →
      19 * k + 1 ∈ exceptionalSplitPrimesNineteen_05 := by
  intro k hk hp
  simp only [Finset.mem_Icc] at hk
  obtain ⟨hk1375, hk1499⟩ := hk
  interval_cases k
  all_goals solve
    | norm_num at hp
    | norm_num [exceptionalSplitPrimesNineteen_05]
