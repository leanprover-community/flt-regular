import ring_theory.fractional_ideal

open_locale big_operators
open polynomial finset module units fractional_ideal submodule


-- TODO redefine span_singleton as a monoid hom so we get this for free?

-- TODO this really shouldn't be necessary either?
@[simp]
lemma fractional_ideal.span_singleton_prod {R : Type*} {P ι : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (T : finset ι) (I : ι → P) :
  span_singleton S (∏ t in T, I t) = ∏ t in T, span_singleton S (I t) :=
begin
  classical,
  induction T using finset.induction with i T hiT ih,
  { simp, },
  simp [hiT, span_singleton_mul_span_singleton, ih.symm],
end

@[simp]
lemma ideal.span_singleton_prod {R ι : Type*} [comm_ring R] (T : finset ι) (I : ι → R) :
  ideal.span ({∏ t in T, I t} : set R) = ∏ t in T, ideal.span {I t} :=
begin
  classical,
  induction T using finset.induction with i T hiT ih,
  { simp, },
  simp [hiT, ideal.span_singleton_mul_span_singleton, ih.symm],
end
