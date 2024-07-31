import Mathlib.RingTheory.FractionalIdeal

open scoped BigOperators

open Polynomial Finset Module Units FractionalIdeal Submodule

-- TODO redefine span_singleton as a monoid hom so we get this for free?
-- TODO this really shouldn't be necessary either?
@[simp]
theorem FractionalIdeal.spanSingleton_prod {R : Type _} {P ι : Type _} [CommRing R]
    {S : Submonoid R} [CommRing P] [Algebra R P] [loc : IsLocalization S P] (T : Finset ι)
    (I : ι → P) : spanSingleton S (∏ t in T, I t) = ∏ t in T, spanSingleton S (I t) := by
  classical
  induction' T using Finset.induction with i T hiT ih
  · simp
  simp [hiT, span_singleton_mul_span_singleton, ih.symm]

