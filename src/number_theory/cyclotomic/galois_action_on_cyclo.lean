import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.number_field_embeddings
import number_theory.cyclotomic.absolute_value

import number_theory.cyclotomic.basic

universes u

open finite_dimensional

variables (p : ℕ+)

local notation `KK` := cyclotomic_field p ℚ

local notation `RR` := number_field.ring_of_integers (cyclotomic_field p ℚ)

local attribute [instance] is_cyclotomic_extension.number_field is_cyclotomic_extension.finite_dimensional

-- @Chris: you mentioned "checking automorphisms agree only on a generator" -
-- what you want is `power_basis.alg_hom_ext`

open_locale number_field

-- we're nearly here!
instance ℤ_cycl_ext : is_cyclotomic_extension {p} ℤ (𝓞 (cyclotomic_field p ℚ)) := sorry

open cyclotomic_ring embeddings

noncomputable theory
open is_cyclotomic_extension
open polynomial

local notation `ζ` := zeta p ℚ KK

@[simp]
lemma minpoly_zeta : minpoly ℚ ζ = cyclotomic p ℚ :=
begin
  rw ← map_cyclotomic_int,
  have : is_primitive_root ζ p := zeta_primitive_root p ℚ (cyclotomic_field p ℚ),
  rw cyclotomic_eq_minpoly this p.pos,
  have : is_integral ℤ ζ,
  from is_primitive_root.is_integral this p.pos,
  have h_mins : minpoly ℚ ζ = (minpoly ℤ ζ).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions ℚ this,
  rw h_mins,
  refl,
end

-- a version of cyclotomic_eq_minpoly
lemma minpoly_primitive_root {z : KK} (h : is_primitive_root z p) : minpoly ℚ z = cyclotomic p ℚ :=
begin
  rw ← map_cyclotomic_int,
  rw cyclotomic_eq_minpoly h p.pos,
  have : is_integral ℤ z,
  from is_primitive_root.is_integral h p.pos,
  have h_mins : minpoly ℚ z = (minpoly ℤ z).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions ℚ this,
  rw h_mins,
  refl,
end

/-- The power basis of the p-th cyclotomic field given by the chosen pth root of unity. -/
def power_basis_zeta_runity : power_basis ℚ KK :=
{ gen := zeta p ℚ KK,
  dim := (minpoly ℚ (zeta p ℚ (cyclotomic_field p ℚ))).nat_degree,
  basis := basis.mk (is_integral.linear_independent_pow
      (is_separable.is_integral ℚ (zeta p ℚ (cyclotomic_field p ℚ)))) sorry,
  basis_eq_pow := by simp }

@[simp]
lemma power_basis_zeta_runity_gen : (power_basis_zeta_runity p).gen = ζ := rfl

/-- complex conjugation as a Galois automorphism -/
def gal_conj : KK →ₐ[ℚ] KK := power_basis.lift (power_basis_zeta_runity p) ζ⁻¹
begin
  simp only [power_basis_zeta_runity_gen, minpoly_zeta],
  have : is_primitive_root ζ p,
  from zeta_primitive_root p ℚ (cyclotomic_field p ℚ),
  have : is_primitive_root ζ⁻¹ p,
  exact is_primitive_root.inv' this,
  rw ← minpoly_primitive_root _ this,
  exact minpoly.aeval _ _,
end

@[simp]
lemma gal_conj_zeta_runity : gal_conj p ζ = ζ⁻¹ := power_basis.lift_gen _ _ _

lemma gal_conj_zeta_runity_pow (n : ℕ) :  gal_conj p (ζ^n) = (ζ⁻¹)^n :=
begin
induction n,
simp only [alg_hom.map_one, pow_zero],
simp only [alg_hom.map_pow, gal_conj_zeta_runity],
end

lemma gal_conj_zeta_runity_coe : gal_conj p (ζ) =  gal_conj p (ζ : KK) :=
begin
refl,
end

open_locale complex_conjugate

lemma conj_norm_one (x : ℂ) (h : complex.abs x = 1) : conj x = x⁻¹ := sorry

@[simp]
lemma embedding_conj (x : KK) (φ : KK →+* ℂ) : conj (φ x) = φ (gal_conj p x) :=
begin
  swap,
  revert x,
  suffices : φ (gal_conj p ζ) = conj (φ ζ),
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  rw conj_norm_one,
  simp [ring_hom.map_inv],
  sorry,
end

lemma gal_conj_idempotent : (gal_conj p).comp (gal_conj p) = (alg_hom.id _ _) :=
begin
  suffices : (gal_conj p ∘ gal_conj p) ζ = (alg_hom.id ℚ _) ζ,
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  simp,
end

-- TODO we should generlize this and have a way to automatically transfer galois automorphisms
-- to automorphisms of the unit group
/-- The conjugate as a map from units to itself -/
def unit_gal_conj : RRˣ → RRˣ :=
λ ⟨u_val, u_inv, u_val_inv, u_inv_val⟩,
  ⟨⟨gal_conj p u_val, sorry⟩, ⟨gal_conj p u_inv, sorry⟩,
  begin
    ext,
    simp only [subalgebra.coe_one, set_like.coe_mk, subalgebra.coe_mul],
    rw ← alg_hom.map_mul,
    rw_mod_cast u_val_inv,
    simp,
  end, begin
    ext,
    simp only [subalgebra.coe_one, set_like.coe_mk, subalgebra.coe_mul],
    rw ← alg_hom.map_mul,
    rw_mod_cast u_inv_val,
    simp,
  end⟩

/-- `unit_gal_conj` as boundled hom. -/
def unit_gal_conj_m : RRˣ →* RRˣ :={
  to_fun := unit_gal_conj  p,
  map_one' := by {simp_rw (unit_gal_conj ),  sorry, },
  map_mul' := by {sorry,},
 }

lemma unit_gal_conj_spec (u : RRˣ) : gal_conj p u = unit_gal_conj p u :=
begin
  cases u,
  simp [unit_gal_conj],
end

lemma uni_gal_conj_inv (u : RRˣ) : (unit_gal_conj p u)⁻¹ = (unit_gal_conj p u⁻¹) :=
begin
rw unit_gal_conj,
simp,
sorry,
end

lemma unit_lemma_val_one (u : RRˣ) (φ : KK →+* ℂ) :
  complex.abs (φ (u * (unit_gal_conj p u)⁻¹)) = 1 :=
begin
  rw ring_hom.map_mul,
  rw complex.abs.is_absolute_value.abv_mul,
  rw ring_hom.map_inv,
  rw is_absolute_value.abv_inv complex.abs,
  rw ← unit_gal_conj_spec,
  rw ← embedding_conj,
  simp [-embedding_conj],
end

lemma unit_gal_conj_idempotent (u : RRˣ) : (unit_gal_conj p (unit_gal_conj p u)) = u :=
begin
   have:=  (unit_gal_conj_spec p u),
   simp at this,
   sorry,
end
