
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

instance {r} [Module A G] (sys : systemOfUnits p G σ r) : Fintype (G ⧸ Submodule.span A (Set.range sys.units)) := sorry

def systemOfUnits.index [Module A G] (sys : systemOfUnits p G σ r) :=
  Fintype.card (G ⧸ Submodule.span A (Set.range sys.units))

def systemOfUnits.IsFundamental [Module A G] (h : systemOfUnits p G σ r) :=
  ∀ s : systemOfUnits p G σ r, h.index ≤ s.index

namespace systemOfUnits
lemma existence' [Module A G] (S : systemOfUnits p G σ R) : ∃ S : systemOfUnits p G σ (R + 1), True := sorry
lemma existence (r) [Module A G] : ∃ S : systemOfUnits p G σ r, True := sorry
end systemOfUnits

noncomputable
abbrev σA : A := MonoidAlgebra.of ℤ H σ
namespace fundamentalSystemOfUnits
lemma existence [Module A G] : ∃ S : systemOfUnits p G σ r, S.IsFundamental := by
  obtain ⟨S⟩ := systemOfUnits.existence p G σ r -- TODO use rank
  have : { a | ∃ S : systemOfUnits p G σ r, a = S.index}.Nonempty := ⟨S.index, S, rfl⟩
  obtain ⟨S', ha⟩ := Nat.sInf_mem this
  use S'
  intro a'
  rw [← ha]
  apply csInf_le (OrderBot.bddBelow _)
  use a'

lemma lemma2 [Module A G] (S : systemOfUnits p G σ r) (hs : S.IsFundamental) (i : Fin r) :
  ∀ g : G, (1 - σA p σ) • g ≠ S.units i := sorry

lemma corollary [Module A G] (S : systemOfUnits p G σ r) (hs : S.IsFundamental) (a : Fin r → ℤ)
    (ha : ∃ i , ¬ (p : ℤ) ∣ a i) :
  ∀ g : G, (1 - σA p σ) • g ≠ ∑ i, a i • S.units i := sorry

end fundamentalSystemOfUnits
section application

variable
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local instance : CommGroup (K ≃ₐ[k] K) := sorry

local notation3 "G" => (𝓞 K)ˣ ⧸ (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : 𝓞 k →* 𝓞 K))

open CommGroup
local instance : Module A (Additive <| G ⧸ torsion G) := sorry
local instance : Module.Free ℤ (Additive <| G ⧸ torsion G) := sorry
lemma Hilbert91ish :
    ∃ S : systemOfUnits p (Additive <| G ⧸ torsion G) σ (NumberField.Units.rank k + 1), S.IsFundamental :=
  fundamentalSystemOfUnits.existence p (Additive <| G ⧸ torsion G) σ

-- #exit


noncomputable

def unitlifts
  ( S : systemOfUnits p (Additive <| G ⧸ torsion G) σ (NumberField.Units.rank k + 1) )  :
  Fin (NumberField.Units.rank k + 1) → Additive (𝓞 K)ˣ := by
  let U := S.units
  intro i
  let u := (((U i)).out').out'
  exact u



lemma Hilbert92
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by

    have S := @Hilbert91ish p K _ k _ _ _ σ
    obtain ⟨S, _⟩ := S
    let H := @unitlifts p K _ k _ _ _ σ  S
    let N : Fin (NumberField.Units.rank k + 1) →  Additive (𝓞 k)ˣ :=
      fun e => Additive.ofMul (Units.map (RingOfIntegers.norm k )) (Additive.toMul (H e))
    have NLI : ¬ LinearIndependent ℤ N := by sorry
    rw [not_linearIndependent_iff] at NLI
    obtain ⟨t, a, ha⟩ := NLI
    by_cases T : Monoid.IsTorsionFree (𝓞 K)ˣ
    let J := Additive.toMul (∑ i in t, a i • H i)
    use J
    constructor
    let r :=   (Additive.toMul (H 1)).1

    have H1 : ∀ i : Fin (NumberField.Units.rank k + 1),
       (Algebra.norm k (( (Additive.toMul (H i)).1) : K)) = ((N i).1 : k) := by
       intro i
       simp
    have H2 : ∏ i in t, ((N i).1 : k)^ a i = 1 := sorry
    simp
    rw [←H2]
    congr
    ext1 v
    simp



    sorry



end application

end thm91
