import number_theory.cyclotomic.cyclotomic_units
/-!
# Galois group of cyclotomic extensions

# References

* [https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf]: this file's main guide.

-/


section to_move

--#11737
lemma pow_eq_pow_iff_modeq {M} [left_cancel_monoid M] (m : M) {x y : ℕ} :
  m ^ x = m ^ y ↔ x ≡ y [MOD (order_of m)] :=
begin
  wlog hxy : x ≤ y,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hxy,
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←mul_one $ m ^ x, pow_add] at h,
    replace h := mul_left_cancel h,
    change x + 0 ≡ x + k [MOD order_of m], --ew
    apply nat.modeq.add_left,
    rw [nat.modeq.comm, nat.modeq_zero_iff_dvd],
    exact order_of_dvd_of_pow_eq_one h.symm },
  { rw [←add_zero x] at h {occs := occurrences.pos [1]},
    replace h := nat.modeq.add_left_cancel' x h,
    rw [nat.modeq.comm, nat.modeq_zero_iff_dvd] at h,
    obtain ⟨k, rfl⟩ := h,
    rw [pow_add, pow_mul, pow_order_of_eq_one, one_pow, mul_one] }
end

-- #11739
@[simps] def is_primitive_root.to_roots_of_unity {M} {μ : M} [comm_monoid M] {n : ℕ+}
  (h : is_primitive_root μ n) : roots_of_unity n M := roots_of_unity.mk_of_pow_eq μ h.pow_eq_one

-- #11738
@[simp] lemma alg_equiv.one_apply {R A} [comm_semiring R] [semiring A] [algebra R A] (r : A) :
  (1 : A ≃ₐ[R] A) r = r := rfl

lemma roots_of_unity.coe_injective {M} [comm_monoid M] {n : ℕ+} :
  function.injective (coe : (roots_of_unity n M) → M) :=
units.ext.comp (λ x y, subtype.ext)

end to_move

-- argument order is for dot-notation
variables {L : Type*} [field L] {μ : L} {n : ℕ+} (hμ : is_primitive_root μ n)
          (K : Type*) [field K]  [algebra K L]

local notation `ζ` := is_cyclotomic_extension.zeta n K L
local notation `ζ'` := is_cyclotomic_extension.zeta_runity n K L

local attribute [instance] pnat.fact_pos

-- should this be `simp` globally?
local attribute [simp] ring_equiv.to_ring_hom_eq_coe

/-- The `monoid_hom` that takes an automorphism to the power of μ that μ gets mapped to under it. -/
@[simps {attrs := []}] noncomputable def is_primitive_root.aut_to_pow  :
  (L ≃ₐ[K] L) →* units (zmod n) :=
let μ' := hμ.to_roots_of_unity in
have ho : order_of μ' = n :=
  by rw [hμ.eq_order_of, ←hμ.coe_to_roots_of_unity_coe, order_of_units, order_of_subgroup],
monoid_hom.to_hom_units
{ to_fun := λ σ, (ring_hom.map_root_of_unity_eq_pow_self σ.to_ring_equiv.to_ring_hom μ').some,
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

open is_cyclotomic_extension

example : true := trivial

example : true := trivial

lemma is_cyclotomic_extension.aut_to_pow_injective [ne_zero (n : K)] : function.injective $
    (@zeta_primitive_root n K L _ _ _ _ _ (ne_zero.of_no_zero_smul_divisors K L)).aut_to_pow K :=
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
