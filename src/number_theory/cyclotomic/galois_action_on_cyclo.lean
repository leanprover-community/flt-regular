import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.absolute_value

import number_theory.cyclotomic.gal

universes u

open finite_dimensional

theorem power_basis.rat_hom_ext {S S' : Type*} [comm_ring S] [hS : algebra ℚ S] [ring S']
  [hS' : algebra ℚ S'] (pb : power_basis ℚ S) ⦃f g : S →+* S'⦄ (h : f pb.gen = g pb.gen) :
f = g :=
let f' := f.to_rat_alg_hom, g' := g.to_rat_alg_hom in
fun_like.ext f g $
by convert fun_like.ext_iff.mp (pb.alg_hom_ext (show f' pb.gen = g' pb.gen, from h))

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
  -- dependent type theory is my favourite
  rw [←ring_hom.comp_apply, ←alg_hom.coe_to_ring_hom, ←ring_hom.comp_apply],
  revert x,
  suffices : φ (gal_conj K p ζ) = conj (φ ζ),
  { rw ←function.funext_iff,
    dsimp only,
    congr' 1,
    symmetry,
    apply (hζ.power_basis ℚ).rat_hom_ext,
    { exact this },
    { exact algebra_rat } },
  rw [conj_norm_one, ←ring_hom.map_inv, gal_conj_zeta_runity hζ],
  -- complex.abs (φ ζ) = 1
  sorry
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
def int_gal (σ : K →ₐ[ℚ] K) : RR →ₐ[ℤ] RR :=
((σ.restrict_scalars ℤ).restrict_domain RR).cod_restrict RR (λ x, gal_map_mem_subtype K x _)

@[simp] lemma int_gal_apply_coe (σ : K →ₐ[ℚ] K) (x : RR) :
  (int_gal σ x : K) = σ x := rfl

/-- Restriction of `σ : K →ₐ[ℚ] K` to the units of the ring of integers.  -/
def units_gal (σ : K →ₐ[ℚ] K) : RRˣ →* RRˣ :=
units.map $ int_gal σ

@[simp] lemma units_gal_apply_coe (σ : K →ₐ[ℚ] K) (x : RRˣ) :
(units_gal σ x : K) = σ x := rfl

/-- `unit_gal_conj` as a bundled hom. -/
def unit_gal_conj : RRˣ →* RRˣ :=
units_gal (gal_conj K p)

lemma unit_gal_conj_spec (u : RRˣ) : gal_conj K p u = unit_gal_conj K p u := rfl

lemma uni_gal_conj_inv (u : RRˣ) : (unit_gal_conj K p u)⁻¹ = (unit_gal_conj K p u⁻¹) := rfl

lemma unit_lemma_val_one (u : RRˣ) (φ : K →+* ℂ) :
  complex.abs (φ (u * (unit_gal_conj K p u)⁻¹)) = 1 :=
begin
  rw [map_mul, complex.abs.is_absolute_value.abv_mul, ring_hom.map_inv,
      complex.abs_inv, ←unit_gal_conj_spec, ←embedding_conj $ zeta_spec p ℚ K],
  simp only [coe_coe, complex.abs_conj, mul_inv_cancel, ne.def, complex.abs_eq_zero,
             ring_hom.map_eq_zero, add_submonoid_class.coe_eq_zero, units.ne_zero, not_false_iff]
end

lemma unit_gal_conj_idempotent (u : RRˣ) : (unit_gal_conj K p (unit_gal_conj K p u)) = u :=
units.ext $ subtype.ext $ by erw [←unit_gal_conj_spec, ←unit_gal_conj_spec, ←alg_hom.comp_apply,
                                  gal_conj_idempotent $ zeta_spec p ℚ K, alg_hom.id_apply, coe_coe]
