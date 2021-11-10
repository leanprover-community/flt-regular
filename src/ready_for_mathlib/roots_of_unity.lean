import ring_theory.roots_of_unity

variables {R : Type*} [comm_ring R] [is_domain R]

open subgroup

lemma is_primitive_root.generator_is_primitive_root_iff_card_roots_of_unity
  {n : ℕ+} (ζ : roots_of_unity n R) (hζ : ∀ x, x ∈ zpowers ζ) :
  is_primitive_root ζ n ↔ fintype.card (roots_of_unity n R) = n :=
begin
  -- I'm really unsure how to remove this yucky double coercion
  refine ⟨λ h, is_primitive_root.card_roots_of_unity (_ : is_primitive_root ((ζ : units R) : R) n),
          λ h, is_primitive_root.mk_of_lt _ _ _ (λ l hl' hl hn, _)⟩,
  { rwa [is_primitive_root.coe_units_iff, is_primitive_root.coe_subgroup_iff] },
  { rw [←h, fintype.card_pos_iff],
    exact ⟨(roots_of_unity.is_cyclic R n).exists_generator.some⟩ },
  { convert pow_order_of_eq_one _,
    rw [←h,order_of_eq_card_of_forall_mem_zpowers hζ] },
  rw ←order_of_eq_card_of_forall_mem_zpowers hζ at h,
  exact pow_eq_one_of_lt_order_of' hl'.ne' (by rwa h) hn
  -- in bump will be renamed to `pow_ne_one_of_lt_order_of'`, the correct name
end
