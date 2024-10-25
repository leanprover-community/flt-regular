import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Localization

open Module
section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

instance torsion.module : Module R (M ⧸ AddCommGroup.torsion M) := by
  letI : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      Nat.isUnit_iff, smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  exact inferInstanceAs (Module R (M ⧸ this))

end
