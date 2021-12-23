import ring_theory.roots_of_unity

namespace is_primitive_root

variables {M : Type*}
variables [comm_monoid M]

variables {k l : ℕ}

variables {ζ : M} (h : is_primitive_root ζ k)

lemma pow_of_div (h : is_primitive_root ζ k) {p : ℕ} (hp : p ≠ 0) (hdiv : p ∣ k) :
  is_primitive_root (ζ ^ p) (k / p) :=
begin
  suffices : order_of (ζ ^ p) = k / p,
  { exact this ▸ is_primitive_root.order_of (ζ ^ p) },
  rw [order_of_pow' _ hp, ← eq_order_of h, nat.gcd_eq_right hdiv]
end

end is_primitive_root
