import Mathlib.NumberTheory.RamificationInertia
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.Lie.OfAssociative

/-!

This file contains lemmas that should go somewhere in a file in mathlib.

-/
open BigOperators UniqueFactorizationMonoid

-- Mathlib/RingTheory/Ideal/Operations.lean
lemma Ideal.comap_coe {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S] [RingHomClass F R S]
  (f : F) (I : Ideal S) : I.comap (f : R →+* S) = I.comap f := rfl

-- Mathlib/RingTheory/IntegralClosure.lean
instance isIntegralClosure_self {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : IsIntegralClosure S R S :=
  ⟨Function.injective_id, fun {x} ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ Algebra.IsIntegral.isIntegral x⟩⟩

-- Mathlib/NumberTheory/RamificationInertia.lean
section RamificationInertia

variable {R S₁ S₂} [CommRing R] [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂]

lemma Ideal.ramificationIdx_comap_eq (e : S₁ ≃ₐ[R] S₂) (p : Ideal R) (P : Ideal S₂) :
    Ideal.ramificationIdx (algebraMap R S₁) p (P.comap e) =
      Ideal.ramificationIdx (algebraMap R S₂) p P := by
  show sSup _ = sSup _
  congr
  ext n
  simp only [Set.mem_setOf_eq, Ideal.map_le_iff_le_comap]
  rw [← Ideal.comap_coe e, ← e.toRingEquiv_toRingHom, Ideal.comap_coe,
    ← RingEquiv.symm_symm (e : S₁ ≃+* S₂), ← Ideal.map_comap_of_equiv, ← Ideal.map_pow,
    Ideal.map_comap_of_equiv, ← Ideal.comap_coe (RingEquiv.symm _), Ideal.comap_comap,
    RingEquiv.symm_symm, e.toRingEquiv_toRingHom, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]

lemma Ideal.inertiaDeg_comap_eq (e : S₁ ≃ₐ[R] S₂) (p : Ideal R) (P : Ideal S₂) [p.IsMaximal] :
    Ideal.inertiaDeg (algebraMap R S₁) p (P.comap e) =
      Ideal.inertiaDeg (algebraMap R S₂) p P := by
  delta Ideal.inertiaDeg
  have : (P.comap e).comap (algebraMap R S₁) = p ↔ P.comap (algebraMap R S₂) = p := by
    rw [← Ideal.comap_coe e, Ideal.comap_comap, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  split
  swap
  · rw [dif_neg]; rwa [← this]
  rw [dif_pos (this.mp ‹_›)]
  apply (config := { allowSynthFailures := true }) LinearEquiv.finrank_eq
  have E := quotientEquivAlg (R₁ := R) (P.comap e) P e
    (Ideal.map_comap_of_surjective _ e.surjective P).symm
  apply (config := {allowSynthFailures := true }) LinearEquiv.mk
  case toLinearMap =>
    apply (config := {allowSynthFailures := true }) LinearMap.mk
    swap
    · exact E.toLinearMap.toAddHom
    · intro r x
      show E (_ * _) = _ * (E x)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [Quotient.mk_comp_algebraMap, Quotient.lift_mk, _root_.map_mul, AlgEquiv.commutes,
        RingHomCompTriple.comp_apply]
  exact E.left_inv
  exact E.right_inv

end RamificationInertia

open Polynomial

open nonZeroDivisors

-- Mathlib/RingTheory/Trace.lean
universe u v in
lemma Algebra.isNilpotent_trace_of_isNilpotent {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (hx : IsNilpotent x) : IsNilpotent (Algebra.trace R S x) := by
  classical
  by_cases hS : ∃ s : Finset S, Nonempty (Basis s R S)
  · obtain ⟨s, ⟨b⟩⟩ := hS
    have := Module.Finite.of_basis b
    have := (Module.free_def.{u, v, v} R S).mpr ⟨s, ⟨b⟩⟩
    apply LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))
  · rw [trace_eq_zero_of_not_exists_basis _ hS, LinearMap.zero_apply]
    exact IsNilpotent.zero

-- Mathlib/Data/Polynomial/Taylor.lean
@[simps] noncomputable
def Polynomial.taylorAlgEquiv {R} [CommRing R] (r : R) : R[X] ≃ₐ[R] R[X] where
  __ := taylorAlgHom r
  invFun := fun p ↦ taylor (-r) p
  left_inv := fun p ↦ by simp [taylor_taylor]
  right_inv := fun p ↦ by simp [taylor_taylor]

-- Mathlib/Data/Polynomial/Taylor.lean
lemma Polynomial.irreducible_taylor_iff {R} [CommRing R] {r} {p : R[X]} :
    Irreducible (taylor r p) ↔ Irreducible p := by
  refine ⟨fun H ↦ H.of_map (f := (taylorAlgEquiv r).toRingEquiv), fun H ↦ ?_⟩
  apply Irreducible.of_map (f := (taylorAlgEquiv r).symm.toRingEquiv)
  simpa only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    taylorAlgEquiv_symm_apply, taylor_taylor, neg_add_cancel, taylor_zero', LinearMap.id_coe, id_eq]

-- Somewhere in polynomial.
lemma Polynomial.dvd_C_mul_X_sub_one_pow_add_one
    {R} [CommRing R] {p : ℕ} (hpri : p.Prime) (hp : p ≠ 2) (a r : R)
    (h₁ : r ∣ a ^ p) (h₂ : r ∣ p * a) : C r ∣ (C a * X - 1) ^ p + 1 := by
  rw [sub_eq_add_neg, add_pow_prime_eq hpri, (hpri.odd_of_ne_two hp).neg_pow, one_pow,
    mul_pow, ← C.map_pow, add_comm, add_comm (_ * _), ← add_assoc, ← add_assoc,
    add_neg_cancel, zero_add]
  refine dvd_add (dvd_mul_of_dvd_left (_root_.map_dvd C h₁) _) ((_root_.map_dvd C h₂).trans ?_)
  rw [map_mul, map_natCast]
  exact mul_dvd_mul_left _ (Finset.dvd_sum (fun x hx ↦ dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_pow (dvd_mul_right _ _) (Finset.mem_Ioo.mp hx).1.ne.symm) _) _))
