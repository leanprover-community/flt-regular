import ring_theory.roots_of_unity
import number_theory.number_field
import field_theory.splitting_field
-- import generalisation_linter
import field_theory.is_alg_closed.basic
import field_theory.polynomial_galois_group
import field_theory.adjoin

open set finite_dimensional complex
open_locale classical
open_locale big_operators
open_locale complex_conjugate

namespace embeddings

noncomputable theory

variables {K L : Type*} [field K] [field L]
section number_field
variables [number_field K] [number_field L]  {n : ℕ} (x : K)


-- TODO generalize to other targets
/-- The equivalence between algebra maps from a number field to the complexes and plain
ring morphisms between them. -/

def equiv_alg : (K →ₐ[ℚ] ℂ) ≃ (K →+* ℂ) :=
{ to_fun := coe,
  inv_fun := λ f : K →+* ℂ, alg_hom.mk' f (λ (c : ℚ) x, map_rat_smul f _ _),
  left_inv  := λ x, alg_hom.ext  $ by simp only [forall_const, alg_hom.coe_to_ring_hom,
                                                 eq_self_iff_true, alg_hom.coe_mk'],
  right_inv := λ x, ring_hom.ext $ by simp only [forall_const, alg_hom.coe_to_ring_hom,
                                                 eq_self_iff_true, alg_hom.coe_mk'] }


lemma lift {L : Type*} [field L] [number_field L] [algebra K L] (φ : K →+* ℂ) :
  ∃ ψ : L →+* ℂ, φ = ψ.comp (algebra_map K L) :=
begin
  letI : algebra K ℂ, from ring_hom.to_algebra φ,
  letI : is_alg_closed ℂ, from complex.is_alg_closed,
  have hS : algebra.is_algebraic K L,
  { show ∀ (a : L), is_algebraic K a,
    intro a,
    obtain ⟨p, hp⟩ := (number_field.is_algebraic L) a,
    haveI : algebra ℚ K, { exact algebra_rat },
    use (polynomial.map (algebra_map ℚ K) p),
    split,
    simp only [ne.def, polynomial.map_eq_zero, not_false_iff, hp.left],
    simp only [polynomial.aeval_map, map_zero, hp.right]
  },
  let ψ₀ : L →ₐ[K] ℂ := is_alg_closed.lift hS,
  let ψ := ψ₀.to_ring_hom,
  use ψ,
  refine fun_like.ext φ (ψ.comp (algebra_map K L)) _,
  intro x,
  show φ x = ψ₀ ((algebra_map K L) x),
  rw alg_hom.commutes ψ₀ x,
  exact rfl,
end

-- There are finitely many complex embeddings of a number field
instance : fintype (K →+* ℂ) := fintype.of_equiv (K →ₐ[ℚ] ℂ) equiv_alg

lemma card_embeddings : fintype.card (K →+* ℂ) = finrank ℚ K :=
by rw [fintype.of_equiv_card equiv_alg, alg_hom.card]

end number_field

variables (φ : K →* ℂ)

/-- An embedding is real if its fixed by complex conjugation-/
def is_real (φ : K →+* ℂ) : Prop := conj ∘ φ = φ

/-- An embedding is real if its not fixed by complex conjugation-/
def is_complex (φ : K →+* ℂ) : Prop := conj ∘ φ ≠ φ

/-- Two embeddings are conjuate if `conj` takes one to the other-/
def are_conj (φ θ : K →+* ℂ) : Prop := conj ∘ φ = θ

/--An element of a number field is real if its image under any embedding is fixed by conj-/
def element_is_real (x : K) : Prop := ∀ φ : K →+* ℂ, conj (φ x) = φ x

local notation `r1` := fintype.card { φ  : K →+* ℂ // is_real φ }

local notation `c2` := fintype.card { φ  : K →+* ℂ // is_complex φ }

lemma not_real_eq_complex (φ : K →+* ℂ) : is_real φ ↔ ¬ is_complex φ :=
begin
  rw [is_real, is_complex],
  simp only [not_not],
end

lemma real_Eq_rank_sub_complex [number_field K] :
  r1 = finrank ℚ K  - c2 :=
begin
  rw ← card_embeddings,
  simp_rw not_real_eq_complex,
  exact fintype.card_subtype_compl _,
end

lemma elem_is_real_is_real (x : K) (h : element_is_real x) :
   ∀  φ : K →+* ℂ, ∃ (r : ℝ), φ x = (r : ℂ) :=
begin
  intro φ,
  simp_rw [element_is_real] at h,
  have h1 := h φ,
  rw eq_conj_iff_real at h1,
  exact h1,
end

/-- A number field all of whose embeddings are real -/
def in_totally_real {K : Type*} [field K] : Prop := ∀ φ : K →+* ℂ, is_real φ

/-- A number field all of whose embeddings are complex -/
def in_totally_complex {K : Type*} [field K] : Prop := ∀ φ : K →+* ℂ, is_complex φ

end embeddings
