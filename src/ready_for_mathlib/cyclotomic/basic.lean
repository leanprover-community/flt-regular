import ready_for_mathlib.cyclotomic
import number_theory.cyclotomic.basic

open polynomial algebra finite_dimensional module set

open_locale big_operators

universes u v w z

variables (n : ℕ+) (S T : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

namespace is_cyclotomic_extension

section cyclotomic_eq_X_pow

variables {A B}

lemma adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic [decidable_eq B] [is_domain B]
  (ζ : B) (hζ : is_primitive_root ζ n) :
  adjoin A (((map (algebra_map A B) (cyclotomic n A)).roots.to_finset) : set B) = adjoin A ({ζ}) :=
begin
  refine le_antisymm (adjoin_le (λ x hx, _)) (adjoin_mono (λ x hx, _)),
  { suffices hx : x ^ ↑n = 1,
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos,
    exact set_like.mem_coe.2 (subalgebra.pow_mem _ (subset_adjoin $ mem_singleton ζ) _),
    rw is_root_of_unity_iff n.pos,
    refine ⟨n, nat.mem_divisors_self n n.ne_zero, _⟩,
    rwa [finset.mem_coe, multiset.mem_to_finset,
         map_cyclotomic, mem_roots $ cyclotomic_ne_zero n B] at hx },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx,
    simpa only [hx, multiset.mem_to_finset, finset.mem_coe, map_cyclotomic,
                mem_roots (cyclotomic_ne_zero n B)] using is_root_cyclotomic n.pos hζ }
end

lemma adjoin_primitive_root_eq_top [is_domain B] [h : is_cyclotomic_extension {n} A B]
  (ζ : B) (hζ : is_primitive_root ζ n) : adjoin A ({ζ} : set B) = ⊤ :=
begin
  classical,
  rw ←adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic n ζ hζ,
  rw adjoin_roots_cyclotomic_eq_adjoin_nth_roots n hζ,
  exact ((iff_adjoin_eq_top {n} A B).mp h).2,
end

end cyclotomic_eq_X_pow

end is_cyclotomic_extension

section is_domain

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

section cyclotomic_ring

namespace cyclotomic_ring

local attribute [instance] cyclotomic_field.algebra_base
local attribute [instance] cyclotomic_ring.algebra_base

lemma eq_adjoin_single (μ : (cyclotomic_field n K))
  (h : μ ∈ primitive_roots n ((cyclotomic_field n K))) :
  cyclotomic_ring n A K = adjoin A ({μ} : set ((cyclotomic_field n K))) :=
begin
  letI := classical.prop_decidable,
  rw [mem_primitive_roots n.pos] at h,
  rw [←is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic n μ h,
      is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots n h],
  simp [cyclotomic_ring]
end

instance [ne_zero ((n : ℕ) : A)] :
  is_fraction_ring (cyclotomic_ring n A K) (cyclotomic_field n K) :=
{ map_units := λ ⟨x, hx⟩, begin
    rw is_unit_iff_ne_zero,
    apply ring_hom.map_ne_zero_of_mem_non_zero_divisors,
    apply adjoin_algebra_injective,
    exact hx
  end,
  surj := λ x,
  begin
    letI : ne_zero ((n : ℕ) : K) := ne_zero.nat_of_injective (is_fraction_ring.injective A K),
    refine algebra.adjoin_induction (((is_cyclotomic_extension.iff_singleton n K _).1
      (cyclotomic_field.is_cyclotomic_extension n K)).2 x) (λ y hy, _) (λ k, _) _ _,
    { exact ⟨⟨⟨y, subset_adjoin hy⟩, 1⟩, by simpa⟩ },
    { have : is_localization (non_zero_divisors A) K := infer_instance,
      replace := this.surj,
      obtain ⟨⟨z, w⟩, hw⟩ := this k,
      refine ⟨⟨algebra_map A _ z, algebra_map A _ w, ring_hom.map_mem_non_zero_divisors _
        (algebra_base_injective n A K) w.2⟩, _⟩,
      letI : is_scalar_tower A K (cyclotomic_field n K) :=
        is_scalar_tower.of_algebra_map_eq (congr_fun rfl),
      rw [set_like.coe_mk, ← is_scalar_tower.algebra_map_apply,
        ← is_scalar_tower.algebra_map_apply, @is_scalar_tower.algebra_map_apply A K _ _ _ _ _
        (_root_.cyclotomic_field.algebra n K) _ _ w, ← ring_hom.map_mul, hw,
        ← is_scalar_tower.algebra_map_apply] },
    { rintro y z ⟨a, ha⟩ ⟨b, hb⟩,
      refine ⟨⟨a.1 * b.2 + b.1 * a.2, a.2 * b.2, mul_mem_non_zero_divisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩,
      rw [set_like.coe_mk, ring_hom.map_mul, add_mul, ← mul_assoc, ha,
        mul_comm ((algebra_map _ _) ↑a.2), ← mul_assoc, hb],
      simp },
    { rintro y z ⟨a, ha⟩ ⟨b, hb⟩,
      refine ⟨⟨a.1 * b.1, a.2 * b.2, mul_mem_non_zero_divisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩,
      rw [set_like.coe_mk, ring_hom.map_mul, mul_comm ((algebra_map _ _) ↑a.2), mul_assoc,
        ← mul_assoc z, hb, ← mul_comm ((algebra_map _ _) ↑a.2), ← mul_assoc, ha],
      simp }
  end,
  eq_iff_exists := λ x y, ⟨λ h, ⟨1, by rw adjoin_algebra_injective n A K h⟩,
    λ ⟨c, hc⟩, by rw mul_right_cancel₀ (non_zero_divisors.ne_zero c.prop) hc⟩ }

end cyclotomic_ring

end cyclotomic_ring

end is_domain
