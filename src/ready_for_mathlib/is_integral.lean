import ring_theory.integral_closure
import linear_algebra.matrix.determinant

namespace matrix

variables {R A n : Type*} [comm_ring R] [comm_ring A] [algebra R A] [fintype n] [decidable_eq n]

lemma det_is_integral {M : matrix n n A} (h : ∀ i j, is_integral R (M i j)) :
  is_integral R M.det :=
begin
  rw [det_apply],
  exact is_integral.sum _ (λ σ hσ, is_integral.zsmul (is_integral.prod _ (λ i hi, h _ _)) _)
end

end matrix
