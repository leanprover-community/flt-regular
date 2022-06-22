import number_theory.cyclotomic.cyclotomic_units
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

open cyclotomic_ring number_field.embeddings

noncomputable theory
open is_cyclotomic_extension
open polynomial

--local notation `ζ` := zeta p ℚ KK

/-- complex conjugation as a Galois automorphism -/
def gal_conj : K →ₐ[ℚ] K :=
↑((is_cyclotomic_extension.aut_equiv_pow K (cyclotomic.irreducible_rat p.pos)).symm (-1))

variables {K p}

lemma zmod.val_neg_one' : ∀ {n : ℕ}, 0 < n → (-1 : zmod n).val = n - 1
| (n + 1) _ := zmod.val_neg_one _

lemma gal_conj_zeta : gal_conj K p (zeta p ℚ K) = (zeta p ℚ K)⁻¹ :=
begin
  let hζ := zeta_spec p ℚ K,
  simp only [gal_conj, units.coe_neg_one, aut_equiv_pow_symm_apply, alg_equiv.coe_alg_hom,
             power_basis.equiv_of_minpoly_apply],
  convert (hζ.power_basis ℚ).lift_gen _ _,
  rw [is_primitive_root.power_basis_gen, zmod.val_neg_one' p.pos,
      pow_sub₀ _ (hζ.ne_zero p.ne_zero) p.pos, pow_one, hζ.pow_eq_one, one_mul]
end

include hζ

@[simp] lemma gal_conj_zeta_runity : gal_conj K p ζ = ζ⁻¹ :=
begin
  obtain ⟨t, ht, rfl⟩ := (zeta_spec p ℚ K).eq_pow_of_pow_eq_one hζ.pow_eq_one p.pos,
  rw [map_pow, gal_conj_zeta, inv_pow]
end

lemma gal_conj_zeta_runity_pow (n : ℕ) :  gal_conj K p (ζ^n) = (ζ⁻¹)^n :=
by rw [map_pow, gal_conj_zeta_runity hζ]

omit hζ

open_locale complex_conjugate

lemma conj_norm_one (x : ℂ) (h : complex.abs x = 1) : conj x = x⁻¹ :=
by rw [←complex.abs_mul_exp_arg_mul_I x, h, complex.of_real_one, one_mul, ←complex.exp_conj,
       ←complex.exp_neg, map_mul, complex.conj_I, mul_neg, complex.conj_of_real]

include hζ

@[simp]
lemma embedding_conj (x : K) (φ : K →+* ℂ) : conj (φ x) = φ (gal_conj K p x) :=
begin
  revert x,
  suffices : φ (gal_conj K p ζ) = conj (φ ζ),
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  -- Eric: this exists as `power_basis.alg_hom_ext`, but this doesn't work here for free.
  rw conj_norm_one; sorry
end

-- `gal_conj` not being an `alg_equiv` makes me very sad
-- but I was determined to make this proof work!
lemma gal_conj_idempotent : (gal_conj K p).comp (gal_conj K p) = (alg_hom.id ℚ K) :=
begin
  convert_to ↑(((aut_equiv_pow K (cyclotomic.irreducible_rat p.pos)).symm (-1)) *
               ((aut_equiv_pow K (cyclotomic.irreducible_rat p.pos)).symm (-1))) = alg_hom.id ℚ K,
  rw [←map_mul, neg_one_mul, neg_neg, map_one],
  refl,
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
