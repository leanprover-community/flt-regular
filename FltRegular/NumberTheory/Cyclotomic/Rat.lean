module

public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The cyclotomic extension instance for `CyclotomicField n ℚ`

Mathlib's instance `IsCyclotomicExtension {n} K (CyclotomicField n K)` for a field `K` of
characteristic zero is stated using the algebra structure `CyclotomicField.algebra n K`. For
`K = ℚ` the algebra structure found by instance search is instead `DivisionRing.toRatAlgebra`,
which is not reducibly defeq to it, so goals stated over `ℚ` do not find the Mathlib instance.
We record the instance in the form that instance search expects.
-/

public section

instance (n : ℕ) : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero n ℚ

end
