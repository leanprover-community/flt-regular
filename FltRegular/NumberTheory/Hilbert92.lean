
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import Mathlib

open scoped NumberField nonZeroDivisors
open FiniteDimensional
open NumberField

variable (p : ℕ+) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open FiniteDimensional BigOperators Finset
-- Z[H] module M (rank L) submodule N (rank l) H-stable
-- H cyclic order p
-- M / N is free up to torsion rank r (as an ab group free rank r p)
-- r = r1 + r2 - 1 = NumberField.Units.rank


section thm91
variable
  (G : Type*) {H : Type*} [AddCommGroup G] [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤)
  [DistribMulAction H G] [Module.Free ℤ G] (hf : finrank ℤ G = r * (p - 1))

local notation3 "A" =>
  MonoidAlgebra ℤ H ⧸ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ H σ) ^ i}

structure systemOfUnits (r : ℕ) [Module A G]
  where
  units : Fin r → G
  linearIndependent : LinearIndependent A units

instance {r}
  [Module A G] -- [IsScalarTower ℤ A G]
  (sys : systemOfUnits (G := G) p σ r) : Fintype (G ⧸ Submodule.span A (Set.range sys.units)) := sorry

structure fundamentalSystemOfUnits (r : ℕ)
    [Module A G] extends systemOfUnits p G σ r -- [IsScalarTower ℤ A G]
  where
  maximal : ∀ a : systemOfUnits p G σ r,
    Fintype.card (G ⧸ Submodule.span A (Set.range units)) ≤ Fintype.card (G ⧸ Submodule.span A (Set.range a.units))

namespace systemOfUnits
lemma existence' [Module A G] (S : systemOfUnits p G σ R) : ∃ S : systemOfUnits p G σ (R + 1), True := sorry
lemma existence [Module A G] : ∃ S : systemOfUnits p G σ r, True := sorry
end systemOfUnits

noncomputable
abbrev σA : A := MonoidAlgebra.of ℤ H σ
namespace fundamentalSystemOfUnits
lemma existence [Module A G] : ∃ S : fundamentalSystemOfUnits p G σ r, True := sorry

lemma lemma2 [Module A G] (S : fundamentalSystemOfUnits p G σ r) (i : Fin r) :
  ∀ g : G, (1 - σA p σ) • g ≠ S.units i := sorry

lemma corollary [Module A G] (S : fundamentalSystemOfUnits p G σ r) (a : Fin r → ℤ)
    (ha : ∃ i , ¬ (p : ℤ) ∣ a i) :
  ∀ g : G, (1 - σA p σ) • g ≠ ∑ i, a i • S.units i := sorry

end fundamentalSystemOfUnits
section application

variable
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local instance : CommGroup (K ≃ₐ[k] K) where
  mul_comm := sorry
local notation3 "G" => (𝓞 K)ˣ ⧸ (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : 𝓞 k →* 𝓞 K))

open CommGroup
local instance : Module A (Additive <| G ⧸ torsion G) := sorry
local instance : Module.Free ℤ (Additive <| G ⧸ torsion G) := sorry
lemma Hilbert91ish :
    ∃ S : fundamentalSystemOfUnits p (Additive <| G ⧸ torsion G) σ (NumberField.Units.rank k + 1), True :=
  fundamentalSystemOfUnits.existence p (Additive <| G ⧸ torsion G) σ
end application

end thm91

-- #exit

lemma Hilbert92
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm K (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := sorry
