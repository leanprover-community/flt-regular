import data.matrix.basic

universes u v w

open_locale matrix big_operators

namespace matrix

lemma mul_transpose_eq_reindex_mul_reindex_transpose {n : Type u} {m : Type v} {R : Type w}
  [fintype n] [fintype m] [semiring R] (e : m ≃ n) (M : matrix n m R) :
  M ⬝ Mᵀ = (reindex (equiv.refl n) e M) ⬝ (reindex (equiv.refl n) e M)ᵀ :=
by rw [reindex_apply, transpose_minor, equiv.refl_symm, equiv.coe_refl,
       minor_mul_equiv, minor_id_id]

end matrix
