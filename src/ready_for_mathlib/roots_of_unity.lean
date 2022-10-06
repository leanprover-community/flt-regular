import ring_theory.roots_of_unity

open polynomial

namespace is_primitive_root

lemma mem_nth_roots_finset {A : Type*} [comm_ring A] [is_domain A] {n : ℕ} {ζ : A}
  (hζ : is_primitive_root ζ n) (hn : 0 < n) : ζ ∈ nth_roots_finset n A :=
(mem_nth_roots_finset hn).2 hζ.pow_eq_one

end is_primitive_root
