import linear_algebra.linear_independent

universes u v w

open_locale big_operators

lemma fintype.linear_independent_iff'' {ι : Type u} {R : Type v} {M : Type w} {v : ι → M}
  [semiring R] [add_comm_monoid M] [module R M] [fintype ι] :
  ¬linear_independent R v ↔ ∃ g : ι → R, (∑ i, g i • v i) = 0 ∧ (∃ i, g i ≠ 0) :=
by simpa using (not_iff_not.2 fintype.linear_independent_iff)
