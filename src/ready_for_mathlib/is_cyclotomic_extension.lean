import number_theory.cyclotomic.basic

universes u v

variables {A : Type u} [comm_ring A] [B : Type v] [comm_ring B] [algebra A B]

namespace is_cyclotomic_extension

open algebra polynomial set subalgebra

lemma adjoin_primitive_root [is_domain B] {ζ : B} {n : ℕ+} (h : is_primitive_root ζ n) :
  is_cyclotomic_extension {n} A (adjoin A ({ζ} : set B)) :=
{ exists_root := λ i hi,
  begin
    rw [set.mem_singleton_iff] at hi,
    refine ⟨⟨ζ, subset_adjoin $ set.mem_singleton ζ⟩, _⟩,
    have := is_root_cyclotomic n.pos h,
    rw [is_root.def, ← map_cyclotomic _ (algebra_map A B), eval_map, ← aeval_def, ← hi] at this,
    rwa [← subalgebra.coe_eq_zero, aeval_subalgebra_coe, subtype.coe_mk]
  end,
  adjoin_roots := λ x,
  begin
    refine adjoin_induction' (λ b hb, _) (λ a, _) (λ b₁ b₂ hb₁ hb₂, _) (λ b₁ b₂ hb₁ hb₂, _) x,
    { rw [set.mem_singleton_iff] at hb,
      refine subset_adjoin _,
      simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq, hb],
      rw [← coe_eq_one, subalgebra.coe_pow, set_like.coe_mk],
      exact ((is_primitive_root.iff_def ζ n).1 h).1 },
    { exact algebra_map_mem _ _ },
    { exact subalgebra.add_mem _ hb₁ hb₂ },
    { exact subalgebra.mul_mem _ hb₁ hb₂ }
  end }

end is_cyclotomic_extension
