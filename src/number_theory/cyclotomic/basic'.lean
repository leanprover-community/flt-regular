import field_theory.abel_ruffini
import ring_theory.polynomial.cyclotomic
import ready_for_mathlib.roots_of_unity
import number_theory.cyclotomic.cyclotomic_units

open polynomial

namespace cyclotomic_extension

variables {F : Type*} [field F]

lemma map_X_pow_sub_one {n k : ℕ} :
  map (algebra_map F (X ^ n - 1 : polynomial F).splitting_field) (X ^ k - 1) = X ^ k - 1 := by simp

lemma has_full_roots_of_unity {n : ℕ+} (hn : (n : F) ≠ 0) :
  fintype.card (roots_of_unity n (X ^ (n : ℕ) - 1 : polynomial F).splitting_field) = n :=
let splf := (X ^ (n : ℕ) - 1 : polynomial F).splitting_field in
begin
  classical,
  rw [fintype.card_congr (roots_of_unity_equiv_nth_roots splf n),
      fintype.card_of_subtype (nth_roots_finset n splf), nth_roots_finset,
      multiset.to_finset_card_of_nodup, nth_roots, C_1, ←map_X_pow_sub_one,
      ←nat_degree_eq_card_roots (splitting_field.splits (X ^ (n : ℕ) - 1 : polynomial F)),
      ←C_1, nat_degree_X_pow_sub_C],
  { apply nodup_roots,
    rw [C_1, ←map_X_pow_sub_one],
    apply separable.map,
    -- depends on #9779 in mathlib, if you want to unsorry this!
    sorry
    /- rw X_pow_sub_one_separable_iff,
    exact_mod_cast hn -/ },
  intro x,
  rw [mem_nth_roots_finset n.pos, mem_nth_roots n.pos]
end

noncomputable def ζ (F : Type*) [field F] (n : ℕ+) :
  roots_of_unity n ((X ^ (n : ℕ) - 1 : polynomial F).splitting_field) :=
(roots_of_unity.is_cyclic _ n).exists_generator.some

def ζ_spec {F : Type*} [field F] {n : ℕ+} : ∀ x, x ∈ subgroup.zpowers (ζ F n) :=
(roots_of_unity.is_cyclic _ n).exists_generator.some_spec

variables {n : ℕ+} (hn : (n : F) ≠ 0)

lemma ζ.is_primitive_root : is_primitive_root (ζ F n) n :=
(is_primitive_root.generator_is_primitive_root_iff_card_roots_of_unity (ζ F n) ζ_spec).mpr $
  has_full_roots_of_unity hn

set_option pp.proofs true

-- a separate project

/-noncomputable lemma gal_embed : (X ^ (n : ℕ) - 1 : polynomial F).gal →* zmod n :=
{ to_fun := λ σ, (σ.to_ring_equiv.to_ring_hom.map_root_of_unity_eq_pow_self $ ζ F n).some,
  map_one' :=
    begin
      have := ((1 : (X ^ (n : ℕ) - 1 : polynomial F).gal).to_ring_equiv.to_ring_hom.map_root_of_unity_eq_pow_self $ ζ F n).some_spec,
      squeeze_simp at this,
    end,
  map_mul' := _ }-/


end cyclotomic_extension
