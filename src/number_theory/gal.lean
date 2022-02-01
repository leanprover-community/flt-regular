import number_theory.cyclotomic.cyclotomic_units
/-!
# Galois group of cyclotomic extensions

# References

* [https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf]: this file's main guide.

-/


section to_move

lemma roots_of_unity.coe_injective {M} [comm_monoid M] {n : ℕ+} :
  function.injective (coe : (roots_of_unity n M) → M) :=
units.ext.comp (λ x y, subtype.ext)

end to_move

-- argument order is for dot-notation

local attribute [instance] pnat.fact_pos

-- should this be `simp` globally?
local attribute [simp] ring_equiv.to_ring_hom_eq_coe

section general

variables {L : Type*} [field L] {μ : L} {n : ℕ+} (hμ : is_primitive_root μ n)
          (K : Type*) [field K] [algebra K L]

local notation `ζ` := is_cyclotomic_extension.zeta n K L
local notation `ζ'` := is_cyclotomic_extension.zeta_runity n K L

/-- The `monoid_hom` that takes an automorphism to the power of μ that μ gets mapped to under it. -/
@[simps {attrs := []}] noncomputable def is_primitive_root.aut_to_pow  :
  (L ≃ₐ[K] L) →* (zmod n)ˣ :=
let μ' := hμ.to_roots_of_unity in
have ho : order_of μ' = n :=
  by rw [hμ.eq_order_of, ←hμ.coe_to_roots_of_unity_coe, order_of_units, order_of_subgroup],
monoid_hom.to_hom_units
{ to_fun := λ σ, (map_root_of_unity_eq_pow_self σ.to_alg_hom μ').some,
  map_one' := begin
    generalize_proofs h1,
    have h := h1.some_spec,
    dsimp only [alg_equiv.one_apply, alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
                ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv] at *,
    replace h : μ' = μ' ^ h1.some := roots_of_unity.coe_injective
                 (by simpa only [roots_of_unity.coe_pow] using h),
    rw ←pow_one μ' at h {occs := occurrences.pos [1]},
    rw [←@nat.cast_one $ zmod n, zmod.nat_coe_eq_nat_coe_iff, ←ho, ←pow_eq_pow_iff_modeq μ', h]
  end,
  map_mul' := begin
    -- well this is absolutely no fun
    generalize_proofs hxy' hx' hy',
    have hxy := hxy'.some_spec,
    have hx := hx'.some_spec,
    have hy := hy'.some_spec,
    dsimp only [alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
                ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv, alg_equiv.mul_apply] at *,
    replace hxy : x (↑μ' ^ hy'.some) = ↑μ' ^ hxy'.some := hy ▸ hxy, -- ow
    rw x.map_pow at hxy,
    replace hxy : ((μ' : L) ^ hx'.some) ^ hy'.some = μ' ^ hxy'.some := hx ▸ hxy,
    rw ←pow_mul at hxy,
    replace hxy : μ' ^ (hx'.some * hy'.some) = μ' ^ hxy'.some := roots_of_unity.coe_injective
                                           (by simpa only [roots_of_unity.coe_pow] using hxy),
    rw [←nat.cast_mul, zmod.nat_coe_eq_nat_coe_iff, ←ho, ←pow_eq_pow_iff_modeq μ', hxy]
  end }

variables (n) [is_cyclotomic_extension {n} K L]

open is_cyclotomic_extension ne_zero

lemma is_cyclotomic_extension.aut_to_pow_injective [ne_zero (n : K)] : function.injective $
    (@zeta_primitive_root n K L _ _ _ _ _ (of_no_zero_smul_divisors K L (n : ℕ))).aut_to_pow K :=
begin
  intros f g hfg,
  apply_fun units.val at hfg,
  simp only [is_primitive_root.coe_aut_to_pow_apply, units.val_eq_coe] at hfg,
  generalize_proofs hf' hg' at hfg,
  have hf := hf'.some_spec,
  have hg := hg'.some_spec,
  dsimp only [alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
              ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv] at hf hg,
  generalize_proofs hζ at hf hg,
  suffices : f hζ.to_roots_of_unity = g hζ.to_roots_of_unity,
  { apply alg_equiv.coe_alg_hom_injective,
    apply (zeta.power_basis n K L).alg_hom_ext,
    exact this },
  rw zmod.eq_iff_modeq_nat at hfg,
  refine (hf.trans _).trans hg.symm,
  rw [←roots_of_unity.coe_pow _ hf'.some, ←roots_of_unity.coe_pow _ hg'.some],
  congr' 1,
  rw [pow_eq_pow_iff_modeq],
  convert hfg,
  rw [hζ.eq_order_of],
  -- any other way gives me motive issues ¯⧹_(ツ)_⧸¯ `change` also solves this
  rw [←hζ.coe_to_roots_of_unity_coe] {occs := occurrences.pos [2]},
  rw [order_of_units, order_of_subgroup]
end

-- this can't be an instance, right? but this is cool!
noncomputable example [ne_zero (n : K)] : comm_group (L ≃ₐ[K] L) :=
function.injective.comm_group _ (is_cyclotomic_extension.aut_to_pow_injective n K) (map_one _)
  (map_mul _) (map_inv _) (map_div _)


variables (L)

-- whilst I can't figure how to make a `power_basis.map_conjugate`, this works
-- for this specific problem
@[simps] noncomputable def zeta_pow_power_basis [ne_zero (n : K)] (t : (zmod n)ˣ) : power_basis K L :=
begin
  haveI := (ne_zero.of_no_zero_smul_divisors K L n).trans,
  refine power_basis.map (algebra.adjoin.power_basis $ integral {n} K L $ ζ ^ (t : zmod n).val) _,
  refine (subalgebra.equiv_of_eq _ _
      (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ _)).trans
      algebra.top_equiv,
  exact (zeta_primitive_root n K L).pow_of_coprime _ (zmod.val_coe_unit_coprime t),
end

end general

section rat

variables (n : ℕ+)

local notation `ℚ[ζₙ]` := cyclotomic_field n ℚ
local notation `ζ` := is_cyclotomic_extension.zeta n ℚ ℚ[ζₙ]
local notation `ζ'` := is_cyclotomic_extension.zeta_runity n ℚ ℚ[ζₙ]

open is_cyclotomic_extension ne_zero

-- yeah I need to fix this mess ASAP
instance im_an_idiot : ne_zero ((n : ℕ) : cyclotomic_field n ℚ) := sorry
instance im_an_idiot2 : ne_zero (n : ℚ) := sorry
instance im_an_idiot3 : ne_zero ((n : ℕ) : ℚ) := sorry
instance : char_zero (cyclotomic_field n ℚ) := sorry

-- oh yay the diamond comes back to hurt us
lemma diamond : cyclotomic_field.algebra n ℚ = algebra_rat :=
@@subsingleton.elim algebra_rat_subsingleton _ _

/-- The `monoid_hom` that takes an automorphism to the power of μ that μ gets mapped to under it. -/
@[simps {attrs := []}] noncomputable lemma cyclotomic_field.rat_aut_equiv_zmod :
  (ℚ[ζₙ] ≃ₐ[ℚ] ℚ[ζₙ]) ≃* (zmod n)ˣ :=
{ inv_fun := λ x, (zeta.power_basis n ℚ ℚ[ζₙ]).equiv_of_minpoly (zeta_pow_power_basis ℚ[ζₙ] n ℚ x)
  (by sorry; begin
    simp only [zeta.power_basis_gen, zeta_pow_power_basis_gen],
    haveI : char_zero (cyclotomic_field n ℚ) := sorry,
    have hl := polynomial.cyclotomic_eq_minpoly_rat (zeta_primitive_root n ℚ ℚ[ζₙ]) n.pos,
    have hr := polynomial.cyclotomic_eq_minpoly_rat
            ((zeta_primitive_root n ℚ ℚ[ζₙ]).pow_of_coprime _ (zmod.val_coe_unit_coprime x)) n.pos,
    convert hl.symm.trans hr; exact diamond n
  end),
  left_inv := sorry,
  right_inv := sorry,
  .. (zeta_primitive_root n ℚ ℚ[ζₙ]).aut_to_pow ℚ }

end rat
