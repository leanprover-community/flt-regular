import ring_theory.roots_of_unity
import number_theory.number_field
import field_theory.splitting_field
-- import generalisation_linter
import field_theory.is_alg_closed.basic
import field_theory.polynomial_galois_group
import field_theory.adjoin
import algebra.char_p.algebra

open_locale classical big_operators complex_conjugate

namespace number_field

noncomputable theory

variables {K L : Type*} [field K] [field L]

variables  {n : ℕ} (x : K)

open set finite_dimensional complex polynomial embeddings

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

lemma real_eq_rank_sub_complex [number_field K] :
  r1 = finrank ℚ K  - c2 :=
begin
  rw ← @card K _ _ ℂ _ _ _,
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
def is_totally_real (K : Type*) [field K] : Prop :=
∀ φ : K →+* ℂ, is_real φ

/-- A number field all of whose embeddings are complex -/
def is_totally_complex (K : Type*) [field K] : Prop :=
∀ φ : K →+* ℂ, is_complex φ

end number_field
