import number_theory.cyclotomic.cyclotomic_units

variables {K : Type*} [field K] {L : Type*} [field L] (n : ℕ+) [algebra K L] [is_cyclotomic_extension {n} K L]

local notation `ζ` := is_cyclotomic_extension.zeta n K L
local notation `ζ'` := is_cyclotomic_extension.zeta_runity n K L

-- well this doesn't exist in mathlib... #11729
lemma pnat.fact_pos : fact (0 < ↑n) := ⟨n.pos⟩

local attribute [instance] pnat.fact_pos

-- should this be `simp` globally?
local attribute [simp] ring_equiv.to_ring_hom_eq_coe

section to_move

-- this is an iff but I don't need the converse
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

end to_move

noncomputable theory

open is_cyclotomic_extension

lemma cyclotomic_field.aut_to_pow [ne_zero (n : K)] :
  (L ≃ₐ[K] L) →* units (zmod n) := monoid_hom.to_hom_units
{ to_fun := λ σ, (ring_hom.map_root_of_unity_eq_pow_self σ.to_ring_equiv.to_ring_hom ζ').some,
  map_one' :=
  by sorry; begin
    haveI : ne_zero ((n : ℕ) : L) := ne_zero.of_no_zero_smul_divisors K L,
    generalize_proofs h,
    have := h.some_spec,
    -- why isn't this somewhere?
    have alg_equiv.one_apply : ∀ l : L, (1 : L ≃ₐ[K] L) l = l := λ x, rfl,
    --simp only [alg_equiv.one_apply, alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
    --           coe_coe, coe_zeta_runity_coe, ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv] at this,
    change (ζ' : L) = (ζ' : L) ^ h.some at this, -- `simp` decides to `eq.rec` the fuck out of `h` for some
                                   -- ungodly reason, but it's "good form" to keep it in I think
    replace this : ζ' = ζ' ^ h.some,
    { suffices h : function.injective ((coe : Lˣ → L) ∘ (coe : (roots_of_unity n L) → Lˣ)),
      { apply h,
        simp only [function.comp_app, ← coe_coe],
        exact_mod_cast this },
      exact units.ext.comp (λ x y, subtype.ext) },
    rw ←pow_one ζ' at this {occs := occurrences.pos [1]},
    have h : order_of ζ' = n,
    { convert (zeta_primitive_root n K L).eq_order_of.symm using 1,
      rw [←coe_zeta_runity_coe, order_of_units, order_of_subgroup] },
    rw [←@nat.cast_one $ zmod n, zmod.nat_coe_eq_nat_coe_iff, ←h, ←pow_eq_pow_iff_modeq ζ'],
    exact this.symm
  end,
  map_mul' := by sorry; begin generalize_proofs hxy hx hy, end }
