import ring_theory.polynomial.cyclotomic

open polynomial

lemma is_root_cyclotomic_iff' {n : ℕ} {K : Type*} [field K] (hpos : 0 < n) {μ : K}
  (h : ∃ ζ : K, is_primitive_root ζ n) : is_primitive_root μ n ↔ is_root (cyclotomic n K) μ :=
begin
  obtain ⟨ζ, hζ⟩ := h,
  rw [← mem_roots (cyclotomic_ne_zero n K), cyclotomic_eq_prod_X_sub_primitive_roots hζ,
    roots_prod_X_sub_C, ← finset.mem_def, ← mem_primitive_roots hpos],
end

lemma is_root_cyclotomic_iff {n : ℕ} {R : Type*} [comm_ring R] [is_domain R] {μ : R}
  : is_primitive_root μ n ↔ is_root (cyclotomic n R) μ := sorry
