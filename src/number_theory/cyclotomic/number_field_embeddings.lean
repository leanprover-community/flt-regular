import ring_theory.roots_of_unity
import number_theory.number_field
import data.real.nnreal
import analysis.special_functions.pow
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

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
variables (φ : K →* ℂ)

-- TODO generalize to other targets
/-- The equivalence between algebra maps from a number field to the complexes and plain
ring morphisms between them. -/

def equiv_alg : (K →ₐ[ℚ] ℂ) ≃ (K →+* ℂ) :=
{ to_fun := coe,
  inv_fun := λ f : K →+* ℂ, alg_hom.mk' f (λ (c : ℚ) x,
    add_monoid_hom.map_rat_module_smul f.to_add_monoid_hom _ _),
  left_inv := begin
    intro f,
    ext x : 1,
    simp,
  end,
  right_inv :=
  begin
    intro f,
    ext x : 1,
    erw alg_hom.coe_mk' f
      (λ (c : ℚ) x, add_monoid_hom.map_rat_module_smul f.to_add_monoid_hom _ _),
  end}

-- There are finitely many complex embeddings of a number field
instance : fintype (K →+* ℂ) := fintype.of_equiv (K →ₐ[ℚ] ℂ) equiv_alg

lemma card_embeddings : fintype.card (K →+* ℂ) = finrank ℚ K :=
by rw [fintype.of_equiv_card equiv_alg, alg_hom.card]

def is_real (φ : K →+* ℂ) : Prop := conj ∘ φ = φ

def is_complex (φ : K →+* ℂ) : Prop := conj ∘ φ ≠ φ

def are_conj (φ θ : K →+* ℂ) : Prop := conj ∘ φ = θ

def element_is_real (x : K) : Prop := ∀  φ : K →+* ℂ, conj (φ x)= φ x

instance  real_embeddings  {K : Type*} [field K] [number_field K] :
  fintype { φ  : K →+* ℂ // is_real φ} := infer_instance

instance complex_embeddings {K : Type*} [field K] [number_field K]:
  fintype { φ : K →+* ℂ // is_complex φ} :=  infer_instance

local notation `r1` := fintype.card { φ  : K →+* ℂ // is_real φ}

local notation `c2` := fintype.card { φ  : K →+* ℂ // is_complex  φ}

lemma not_real_eq_complex (φ : K →+* ℂ) : is_real φ ↔ ¬ is_complex φ :=
begin
  rw [is_real, is_complex],
  simp,
end

lemma real_Eq_rank_sub_complex :
  r1 = finrank ℚ K  - c2 :=
begin
  rw ← card_embeddings,
  convert  fintype.card_subtype_compl, simp, simp_rw ← not_real_eq_complex,
end



end embeddings
