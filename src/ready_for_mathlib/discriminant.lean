import ready_for_mathlib.is_integral
import ring_theory.discriminant

namespace algebra

open matrix

variables {R K L ι : Type*} [comm_ring R] [field K] [field L] [fintype ι] [decidable_eq ι]
variables [algebra R K] [algebra K L] [algebra R L][is_scalar_tower R K L] [finite_dimensional K L]

lemma discr_is_integral {b : ι → L} (h : ∀ i, _root_.is_integral R (b i)) :
  _root_.is_integral R (discr K b) :=
begin
  rw [discr_def],
  exact det_is_integral (λ i j, is_integral_trace (is_integral_mul (h i) (h j)))
end

end algebra
