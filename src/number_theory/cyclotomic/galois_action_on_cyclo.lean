import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.number_field_embeddings
import number_theory.cyclotomic.absolute_value

import number_theory.cyclotomic.gal

universes u

open finite_dimensional

variables (K : Type*) (p : ℕ+) [field K] [char_zero K] [is_cyclotomic_extension {p} ℚ K]
variables {ζ : K} (hζ : is_primitive_root ζ p)

--local notation `KK` := cyclotomic_field p ℚ

local notation `RR` := number_field.ring_of_integers K

-- @Chris: you mentioned "checking automorphisms agree only on a generator" -
-- what you want is `power_basis.alg_hom_ext`

open_locale number_field cyclotomic

open cyclotomic_ring embeddings

noncomputable theory
open is_cyclotomic_extension
open polynomial

--local notation `ζ` := zeta p ℚ KK

/-- complex conjugation as a Galois automorphism -/
def gal_conj : K →ₐ[ℚ] K :=
((is_cyclotomic_extension.aut_equiv_pow _ (cyclotomic.irreducible_rat p.pos)).symm (-1)).to_alg_hom

variables {K p}

@[simp]
lemma gal_conj_zeta_runity : gal_conj K p ζ = ζ⁻¹ := sorry

lemma gal_conj_zeta_runity_pow (n : ℕ) :  gal_conj K p (ζ^n) = (ζ⁻¹)^n :=
begin
sorry
end

open_locale complex_conjugate

lemma conj_norm_one (x : ℂ) (h : complex.abs x = 1) : conj x = x⁻¹ := sorry

include hζ

@[simp]
lemma embedding_conj (x : K) (φ : K →+* ℂ) : conj (φ x) = φ (gal_conj K p x) :=
begin
  swap,
  revert x,
  suffices : φ (gal_conj K p ζ) = conj (φ ζ),
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  rw conj_norm_one,
  simp [ring_hom.map_inv],
  sorry,
end

lemma gal_conj_idempotent : (gal_conj K p).comp (gal_conj K p) = (alg_hom.id ℚ K) :=
begin
  suffices : (gal_conj K p ∘ gal_conj K p) ζ = (alg_hom.id ℚ _) ζ,
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  simp,
end

omit hζ

variable (p)

--generalize this
lemma gal_map_mem {x : K} (hx : x ∈ RR) (σ : K →ₐ[ℚ] K) : σ x ∈ RR :=
is_integral_alg_hom (σ.restrict_scalars ℤ) hx

lemma gal_map_mem_subtype (x : RR) (σ : K →ₐ[ℚ] K) : σ x ∈ RR :=
by simp [gal_map_mem]

/-- Restriction of `σ : K →ₐ[ℚ] K` to the ring of integers.  -/
@[simps] def int_gal (σ : K →ₐ[ℚ] K) : RR →ₐ[ℤ] RR :=
((σ.restrict_scalars ℤ).restrict_domain RR).cod_restrict RR (λ x, gal_map_mem_subtype K x _)

/-- Restriction of `σ : K →ₐ[ℚ] K` to the units of the ring of integers.  -/
@[simps] def units_gal (σ : K →ₐ[ℚ] K) : RRˣ →* RRˣ :=
units.map $ int_gal σ

/-- `unit_gal_conj` as a bundled hom. -/
@[simps] def unit_gal_conj : RRˣ →* RRˣ :=
units_gal (gal_conj K p)

lemma unit_gal_conj_spec (u : RRˣ) : gal_conj K p u = unit_gal_conj K p u :=
begin
  cases u,
  simp [unit_gal_conj],
  sorry
end

lemma uni_gal_conj_inv (u : RRˣ) : (unit_gal_conj K p u)⁻¹ = (unit_gal_conj K p u⁻¹) :=
begin
rw unit_gal_conj,
simp,
end

lemma unit_lemma_val_one (u : RRˣ) (φ : K →+* ℂ) :
  complex.abs (φ (u * (unit_gal_conj K p u)⁻¹)) = 1 :=
begin
  rw ring_hom.map_mul,
  rw complex.abs.is_absolute_value.abv_mul,
  rw ring_hom.map_inv,
  rw is_absolute_value.abv_inv complex.abs,
  rw ← unit_gal_conj_spec,
  rw ← embedding_conj,
  simp [-embedding_conj],
  sorry,
  sorry,
end

lemma unit_gal_conj_idempotent (u : RRˣ) : (unit_gal_conj K p (unit_gal_conj K p u)) = u :=
begin
   have:=  (unit_gal_conj_spec K p u),
   simp at this,
   sorry,
end
