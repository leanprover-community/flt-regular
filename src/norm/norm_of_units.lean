import ring_theory.norm
import number_theory.number_field
import ready_for_mathlib.is_integral

-- mapping `is_integral`: `is_integral_alg_hom` (I'd rename to `is_integral.map` for dot notation)

open_locale number_field

open finset number_field

namespace algebra

/-- The norm on the ring of integers. -/
@[simps] noncomputable def norm' (K) {L} [field K] [field L] [algebra K L]
  [is_separable K L] [finite_dimensional K L] : (π L) β* (π K) :=
((algebra.norm K).restrict (π L)).cod_restrict (π K) (Ξ» x, algebra.is_integral_norm K x.2)

variables {K L : Type*} [field K] [field L] [algebra K L] [finite_dimensional K L] {x y : π L}
variables (K)

open_locale big_operators

section using_cursed_algebra_instance

-- this instance creates half of the world's diamonds, don't touch this
local attribute [instance] number_field.ring_of_integers_algebra

lemma algebra_map_norm' [is_separable K L] (x : π L) :
  (algebra_map (π K) (π L) (norm' K x) : L) = algebra_map K L (norm K (x : L)) := rfl

lemma norm_unit_iff [is_galois K L] : is_unit x β is_unit (norm' K x) :=
begin
  classical,
  refine β¨is_unit.map _, Ξ» hx, _β©,
  replace hx : is_unit (algebra_map (π K) (π L) $ norm' K x) := hx.map (algebra_map (π K) $ π L),
  refine @is_unit_of_mul_is_unit_right (π L) _
         β¨(finset.univ \ { alg_equiv.refl }).prod (Ξ» (Ο : L ββ[K] L), Ο x),
          prod_mem (Ξ» Ο hΟ, is_integral_alg_hom (Ο : L β+* L).to_int_alg_hom x.2)β© _ _,
  convert hx using 1,
  ext,
  push_cast,
  convert_to (finset.univ \ { alg_equiv.refl }).prod (Ξ» (Ο : L ββ[K] L), Ο x) * (β (Ο : L ββ[K] L) in {alg_equiv.refl}, Ο (x : L)) = _,
  { rw [finset.prod_singleton, alg_equiv.coe_refl, id] },
  rw [finset.prod_sdiff $ finset.subset_univ _, βnorm_eq_prod_automorphisms],
  refl, -- this should probably get removed, it's a medium-heavy refl and should be replaced
  -- with proper lemmas for `ring_of_integers_algebra`
end

variable (x)

lemma dvd_norm [is_galois K L] : x β£ algebra_map (π K) (π L) (norm' K x) :=
begin
  classical,
  have : algebra_map K L (norm K x.1) = _ := norm_eq_prod_automorphisms K, --make x explicit
  rw [β insert_erase (mem_univ alg_equiv.refl), prod_insert (not_mem_erase alg_equiv.refl
    (univ : finset (L ββ[K] L))), subtype.val_eq_coe, alg_equiv.coe_refl, id.def] at this,
  have hint : (β (Ο : L ββ[K] L) in univ.erase alg_equiv.refl, Ο x) β π L :=
    subalgebra.prod_mem _ (Ξ» Ο hΟ, (mem_ring_of_integers _ _).2
    (Ο.to_alg_hom.is_integral_of_is_scalar_tower (ring_of_integers.is_integral_coe x))),
  refine β¨β¨_, hintβ©, subtype.ext _β©,
  rw [algebra_map_norm' K x, norm_eq_prod_automorphisms],
  simp only [mul_mem_class.coe_mul, set_like.coe_mk],
  nth_rewrite 0 [β insert_erase (mem_univ alg_equiv.refl)],
  rw [prod_insert (not_mem_erase alg_equiv.refl (univ : finset (L ββ[K] L)))],
  refl, --simp instead of rw in the previous line produces a strange error
end

end using_cursed_algebra_instance

end algebra
