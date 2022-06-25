import ring_theory.norm
import number_theory.number_field
import ready_for_mathlib.is_integral

-- mapping `is_integral`: `is_integral_alg_hom` (I'd rename to `is_integral.map` for dot notation)

open_locale number_field

open finset number_field

namespace algebra

/-- The norm on the ring of integers. -/
@[simps] noncomputable def norm' (K) {L} [field K] [field L] [algebra K L]
  [is_separable K L] [finite_dimensional K L] : (𝓞 L) →* (𝓞 K) :=
((algebra.norm K).restrict (𝓞 L)).cod_restrict (𝓞 K) (λ x, algebra.is_integral_norm K x.2)

variables {K L : Type*} [field K] [field L] [algebra K L] [finite_dimensional K L] {x y : 𝓞 L}
variables (K)

lemma cast_norm' [is_separable K L] (x : 𝓞 L) : (norm' K x : K) = norm K (x : L) := rfl

open_locale big_operators

section using_cursed_algebra_instance

-- this instance creates half of the world's diamonds, don't touch this
local attribute [instance] number_field.ring_of_integers_algebra

lemma algebra_map_norm' [is_separable K L] (x : 𝓞 L) :
  (algebra_map (𝓞 K) (𝓞 L) (norm' K x) : L) = algebra_map K L (norm K (x : L)) := rfl

lemma norm_unit_iff [is_galois K L] : is_unit x ↔ is_unit (norm' K x) :=
begin
  classical,
  refine ⟨is_unit.map _, λ hx, _⟩,
  replace hx : is_unit (algebra_map (𝓞 K) (𝓞 L) $ norm' K x) := hx.map (algebra_map (𝓞 K) $ 𝓞 L),
  refine @is_unit_of_mul_is_unit_right (𝓞 L) _
         ⟨(finset.univ \ { alg_equiv.refl }).prod (λ (σ : L ≃ₐ[K] L), σ x),
          prod_mem (λ σ hσ, is_integral_alg_hom (σ : L →+* L).to_int_alg_hom x.2)⟩ _ _,
  convert hx using 1,
  ext,
  push_cast,
  convert_to (finset.univ \ { alg_equiv.refl }).prod (λ (σ : L ≃ₐ[K] L), σ x) * (∏ (σ : L ≃ₐ[K] L) in {alg_equiv.refl}, σ (x : L)) = _,
  { rw [finset.prod_singleton, alg_equiv.coe_refl, id] },
  rw [finset.prod_sdiff $ finset.subset_univ _, ←norm_eq_prod_automorphisms],
  refl, -- this should probably get removed, it's a medium-heavy refl and should be replaced
  -- with proper lemmas for `ring_of_integers_algebra`
end

variable (x)

lemma dvd_norm [is_galois K L] : x ∣ algebra_map (𝓞 K) (𝓞 L) (norm' K x) :=
begin
  classical,
  have : algebra_map K L (norm K x.1) = _ := norm_eq_prod_automorphisms K, --make x explicit
  rw [← insert_erase (mem_univ alg_equiv.refl), prod_insert (not_mem_erase alg_equiv.refl
    (univ : finset (L ≃ₐ[K] L))), subtype.val_eq_coe, alg_equiv.coe_refl, id.def] at this,
  have hint : (∏ (σ : L ≃ₐ[K] L) in univ.erase alg_equiv.refl, σ x) ∈ 𝓞 L :=
    subalgebra.prod_mem _ (λ σ hσ, (mem_ring_of_integers _ _).2
    (σ.to_alg_hom.is_integral_of_is_scalar_tower (ring_of_integers.is_integral_coe x))),
  refine ⟨⟨_, hint⟩, subtype.ext _⟩,
  rw [algebra_map_norm' K x, norm_eq_prod_automorphisms],
  simp only [mul_mem_class.coe_mul, set_like.coe_mk],
  nth_rewrite 0 [← insert_erase (mem_univ alg_equiv.refl)],
  rw [prod_insert (not_mem_erase alg_equiv.refl (univ : finset (L ≃ₐ[K] L)))],
  refl, --simp instead of rw in the previous line produces a strange error
end

end using_cursed_algebra_instance

end algebra
