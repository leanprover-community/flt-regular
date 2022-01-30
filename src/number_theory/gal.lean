import number_theory.cyclotomic.cyclotomic_units

variables {K : Type*} [field K] {L : Type*} [field L] (n : ℕ+) [algebra K L]

local notation `ζ` := is_cyclotomic_extension.zeta n K L
local notation `ζ'` := is_cyclotomic_extension.zeta_runity n K L

local attribute [instance] pnat.fact_pos

-- should this be `simp` globally?
local attribute [simp] ring_equiv.to_ring_hom_eq_coe

section to_move

lemma pow_eq_pow_iff_modeq {M} [left_cancel_monoid M] (m : M) {x y : ℕ} :
  m ^ x = m ^ y ↔ x ≡ y [MOD (order_of m)] :=
begin
  wlog hxy : x ≤ y,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hxy,
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←mul_one $ m ^ x, pow_add] at h,
    replace h := mul_left_cancel h,
    sorry, /- I'm lazy, sleepy, and want to watch Rafa destroy Medvedev tomorrow -/ },
  { rw [←add_zero x] at h {occs := occurrences.pos [1]},
    replace h := nat.modeq.add_left_cancel' x h,
    rw [nat.modeq.comm, nat.modeq_zero_iff_dvd] at h,
    obtain ⟨k, rfl⟩ := h,
    rw [pow_add, pow_mul, pow_order_of_eq_one, one_pow, mul_one] }
end

@[simps] def is_primitive_root.to_roots_of_unity {M} {μ : M} [comm_monoid M] {n : ℕ+}
  (h : is_primitive_root μ n) : roots_of_unity n M := roots_of_unity.mk_of_pow_eq μ h.pow_eq_one

@[simp] lemma alg_equiv.one_apply {R A} [comm_semiring R] [semiring A] [algebra R A] (r : A) :
  (1 : A ≃ₐ[R] A) r = r := rfl

end to_move

noncomputable def is_primitive_root.aut_to_pow {μ : L} (hμ : is_primitive_root μ n) :
  (L ≃ₐ[K] L) →* units (zmod n) :=
let μ' := hμ.to_roots_of_unity in
have ho : order_of μ' = n := by { convert hμ.eq_order_of.symm using 1,
      rw [←is_primitive_root.coe_to_roots_of_unity_coe hμ, order_of_units, order_of_subgroup] },
have hcc : function.injective ((coe : Lˣ → L) ∘ (coe : (roots_of_unity n L) → Lˣ)) :=
  units.ext.comp (λ x y, subtype.ext),
monoid_hom.to_hom_units
{ to_fun := λ σ, (ring_hom.map_root_of_unity_eq_pow_self σ.to_ring_equiv.to_ring_hom μ').some,
  map_one' := begin
    generalize_proofs h1,
    have h := h1.some_spec,
    dsimp only [alg_equiv.one_apply, alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
                ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv] at *,
    replace h : μ' = μ' ^ h1.some :=
      hcc (by simpa only [function.comp_app, ←coe_coe, roots_of_unity.coe_pow] using h),
    rw ←pow_one μ' at h {occs := occurrences.pos [1]},
    rw [←@nat.cast_one $ zmod n, zmod.nat_coe_eq_nat_coe_iff, ←ho, ←pow_eq_pow_iff_modeq μ', h]
  end,
  map_mul' := begin
    -- well this is absolutely no fun
    generalize_proofs hxy' hx' hy',
    have hxy := hxy'.some_spec,
    have hx := hx'.some_spec,
    have hy := hy'.some_spec,
    dsimp only [alg_equiv.one_apply, alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
                ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv, alg_equiv.mul_apply] at *,
    replace hxy : x (↑μ' ^ hy'.some) = ↑μ' ^ hxy'.some := hy ▸ hxy, -- ow
    rw x.map_pow at hxy,
    replace hxy : ((μ' : L) ^ hx'.some) ^ hy'.some = μ' ^ hxy'.some := hx ▸ hxy,
    rw ←pow_mul at hxy,
    replace hxy : μ' ^ (hx'.some * hy'.some) = μ' ^ hxy'.some :=
      hcc (by simpa only [function.comp_app, ←coe_coe, roots_of_unity.coe_pow] using hxy),
    rw [←nat.cast_mul, zmod.nat_coe_eq_nat_coe_iff, ←ho, ←pow_eq_pow_iff_modeq μ', hxy]
  end }
