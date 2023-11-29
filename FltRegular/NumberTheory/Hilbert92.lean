
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import Mathlib

set_option autoImplicit false
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
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (r : ℕ)
  [DistribMulAction H G] [Module.Free ℤ G] (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
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

lemma existence0 [Module A G] : Nonempty (systemOfUnits p G σ 0) := by
    refine ⟨⟨fun _ => 0, linearIndependent_empty_type⟩⟩

lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G σ R) (hR : R < r) :
        Nonempty (systemOfUnits p G σ (R + 1)) := sorry

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ r) :  Nonempty (systemOfUnits p G σ R) := by
    induction R with
    | zero => exact existence0 p G σ
    | succ n ih =>
        obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
        exact existence' p G σ r S (lt_of_lt_of_le (Nat.lt.base n) hR)

lemma existence (r) [Module A G] : Nonempty (systemOfUnits p G σ r) := existence'' p G σ r rfl.le


end systemOfUnits

noncomputable
abbrev σA : A := MonoidAlgebra.of ℤ H σ
namespace fundamentalSystemOfUnits
lemma existence [Module A G] : ∃ S : systemOfUnits p G σ r, S.IsFundamental := by
  obtain ⟨S⟩ := systemOfUnits.existence p G σ r
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
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] [IsCyclic (K ≃ₐ[k] K)] -- technically redundant but useful
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

-- local instance : CommGroup (K ≃ₐ[k] K) where
--   mul_comm := by
--     have : Fintype.card (K ≃ₐ[k] K) = p := by
--       rwa [IsGalois.card_aut_eq_finrank]
--     have : IsCyclic (K ≃ₐ[k] K) := isCyclic_of_prime_card (hp := ⟨hp⟩) this
--     use IsCyclic.commGroup.mul_comm

local notation3 "G" => (𝓞 K)ˣ ⧸ (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : 𝓞 k →* 𝓞 K))

attribute [local instance] IsCyclic.commGroup

open CommGroup
instance : MulDistribMulAction (K ≃ₐ[k] K) (𝓞 K)ˣ := sorry
instance : MulDistribMulAction (K ≃ₐ[k] K) G := sorry
-- instance : DistribMulAction (K ≃ₐ[k] K) (Additive G) := inferInstance
def ρ : Representation ℤ (K ≃ₐ[k] K) (Additive G) := Representation.ofMulDistribMulAction _ _
noncomputable
instance foof : Module
  (MonoidAlgebra ℤ (K ≃ₐ[k] K))
  (Additive G) := Representation.asModuleModule (ρ (k := k) (K := K))

lemma tors1 (a : Additive G) :
    (∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i) • a = 0 := by
  rw [sum_smul]
  simp only [MonoidAlgebra.of_apply]
  sorry

lemma tors2 (a : Additive G) (t)
    (ht : t ∈ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) :
    t • a = 0 := by
  simp only [one_pow, Ideal.mem_span_singleton] at ht
  obtain ⟨r, rfl⟩ := ht
  let a': Module
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G) := foof
  let a'': MulAction
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G) := inferInstance
  rw [mul_comm, mul_smul]
  let a''': MulActionWithZero
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G) := inferInstance
  rw [tors1 p σ a, smul_zero] -- TODO this is the worst proof ever maybe because of sorries

lemma isTors : Module.IsTorsionBySet
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G)
    (Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i} : Set _) := by
  intro a s
  rcases s with ⟨s, hs⟩
  simp only [MonoidAlgebra.of_apply, one_pow, SetLike.mem_coe] at hs -- TODO ew why is MonoidAlgebra.single_pow simp matching here
  have := tors2 p σ a s hs
  simpa
noncomputable
local instance : Module
  (MonoidAlgebra ℤ (K ≃ₐ[k] K) ⧸
    Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) (Additive G) :=
(isTors (k := k) (K := K) p σ).module

def tors : Submodule
  (MonoidAlgebra ℤ (K ≃ₐ[k] K) ⧸
    Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) (Additive G) := sorry
-- local instance : Module A (Additive G ⧸ AddCommGroup.torsion (Additive G)) := Submodule.Quotient.module _
#synth CommGroup G
#synth AddCommGroup (Additive G)
-- #check Submodule.Quotient.module (tors (k := k) (K := K) p σ)
local instance : Module A (Additive G ⧸ tors (k := k) (K := K) p σ) := by
  -- apply Submodule.Quotient.modue _
  sorry
local instance : Module.Free ℤ (Additive <| G ⧸ torsion G) := sorry
-- #exit
lemma Hilbert91ish :
    ∃ S : systemOfUnits p (Additive G ⧸ tors (k := k) (K := K) p σ) σ (NumberField.Units.rank k + 1), S.IsFundamental :=
  fundamentalSystemOfUnits.existence p (Additive G ⧸ tors (k := k) (K := K) p σ) σ (NumberField.Units.rank k + 1)
end application

end thm91

-- #exit

lemma Hilbert92
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := sorry
