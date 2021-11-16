import data.polynomial.eval

open_locale big_operators

open polynomial

lemma is_root_prod {R : Type*} [comm_ring R] [is_domain R] {ι : Type*}
  (s : finset ι) (p : ι → polynomial R) (x : R) :
  is_root (∏ j in s, p j) x ↔ ∃ i ∈ s, is_root (p i) x :=
by simp only [is_root, eval_prod, finset.prod_eq_zero_iff]

lemma is_root_map {R S : Type*} [comm_ring R] [comm_semiring S] {f : R →+* S} {x : R}
  {p : polynomial R} (hf : function.injective f) : is_root p x ↔ is_root (p.map f) (f x) :=
by simp only [is_root, eval_map, eval₂_hom, f.injective_iff'.mp hf]
