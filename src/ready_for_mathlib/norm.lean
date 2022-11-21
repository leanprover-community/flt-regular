import ring_theory.norm
import number_theory.number_field.basic

open_locale number_field big_operators

open finset number_field

namespace algebra

variables {L : Type*} (K : Type*) [field K] [field L] [algebra K L] [finite_dimensional K L]

/-- The norm on the ring of integers. -/
@[simps] noncomputable def norm' [is_separable K L] : (𝓞 L) →* (𝓞 K) :=
((norm K).restrict (𝓞 L)).cod_restrict (𝓞 K) (λ x, is_integral_norm K x.2)

local attribute [instance] number_field.ring_of_integers_algebra

lemma algebra_map_norm' [is_separable K L] (x : 𝓞 L) :
  (algebra_map (𝓞 K) (𝓞 L) (norm' K x) : L) = algebra_map K L (norm K (x : L)) := rfl

lemma norm'_unit_iff [is_galois K L] {x : 𝓞 L} :
  is_unit (norm' K x) ↔ is_unit x :=
begin
  classical,
  refine ⟨λ hx, _, is_unit.map _⟩,
  replace hx : is_unit (algebra_map (𝓞 K) (𝓞 L) $ norm' K x) := hx.map (algebra_map (𝓞 K) $ 𝓞 L),
  refine @is_unit_of_mul_is_unit_right (𝓞 L) _
         ⟨(univ \ { alg_equiv.refl }).prod (λ (σ : L ≃ₐ[K] L), σ x),
          prod_mem (λ σ hσ, map_is_integral (σ : L →+* L).to_int_alg_hom x.2)⟩ _ _,
  convert hx using 1,
  ext,
  push_cast,
  convert_to (univ \ { alg_equiv.refl }).prod (λ (σ : L ≃ₐ[K] L), σ x) * (∏ (σ : L ≃ₐ[K] L) in
    {alg_equiv.refl}, σ (x : L)) = _,
  { rw [prod_singleton, alg_equiv.coe_refl, id] },
  { rw [prod_sdiff $ subset_univ _, ←norm_eq_prod_automorphisms, algebra_map_norm'] }
end

lemma dvd_norm' [is_galois K L] (x : 𝓞 L) : x ∣ algebra_map (𝓞 K) (𝓞 L) (norm' K x) :=
begin
  classical,
  have : algebra_map K L (norm K x.1) = _ := norm_eq_prod_automorphisms K, --make x explicit
  rw [← insert_erase (mem_univ alg_equiv.refl), prod_insert (not_mem_erase alg_equiv.refl
    (univ : finset (L ≃ₐ[K] L))), subtype.val_eq_coe, alg_equiv.coe_refl, id.def] at this,
  have hint : (∏ (σ : L ≃ₐ[K] L) in univ.erase alg_equiv.refl, σ x) ∈ 𝓞 L :=
    subalgebra.prod_mem _ (λ σ hσ, (mem_ring_of_integers _ _).2
    (map_is_integral σ (ring_of_integers.is_integral_coe x))),
  refine ⟨⟨_, hint⟩, subtype.ext _⟩,
  rw [algebra_map_norm' K x, norm_eq_prod_automorphisms],
  simp only [mul_mem_class.coe_mul, set_like.coe_mk],
  nth_rewrite 0 [← insert_erase (mem_univ alg_equiv.refl)],
  rw [prod_insert (not_mem_erase alg_equiv.refl (univ : finset (L ≃ₐ[K] L)))],
  simp
end

end algebra
