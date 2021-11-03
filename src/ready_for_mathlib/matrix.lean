import data.matrix.basic

universes u v w

open_locale matrix big_operators

namespace matrix

lemma mul_transpose_eq_reindex_mul_reindex_transpose {n : Type u} {m : Type v} {R : Type w}
  [fintype n] [fintype m] [semiring R] (e : m ≃ n) (M : matrix n m R) :
  M ⬝ Mᵀ = (reindex (equiv.refl n) e M) ⬝ (reindex (equiv.refl n) e M)ᵀ :=
funext $ λ _, funext $ λ _, fintype.sum_equiv e _ _ (λ _, by simp)

end matrix
