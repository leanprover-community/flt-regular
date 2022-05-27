import ring_theory.dedekind_domain.ideal
import algebra.big_operators.finsupp

variables {α : Type*} [comm_ring α] [is_domain α] [is_dedekind_domain α]

example (p : nat) (a b c : ideal α) (cp : is_coprime a b) (h : a*b = c^p) (hb : b ≠ 0) :
  ∃ d : ideal α, a = d ^ p :=
begin
  classical,
  obtain rfl|ha := eq_or_ne a 0,
  { use 0, apply (zero_pow _).symm, contrapose! h,
    rw le_zero_iff at h, rw [h, pow_zero, zero_mul], exact zero_ne_one },
  let fa := unique_factorization_monoid.normalized_factors a,
  let fb := unique_factorization_monoid.normalized_factors b,
  let fc := unique_factorization_monoid.normalized_factors c,
  have : ∀ d ∈ fa, d ∉ fb,
  { intros d ha hb,
    have := unique_factorization_monoid.irreducible_of_normalized_factor _ ha,
    apply irreducible.not_unit this,
    apply is_coprime.is_unit_of_dvd' cp;
    apply unique_factorization_monoid.dvd_of_mem_normalized_factors;
    assumption },
  suffices : ∃ f : multiset (ideal α), fa = p • f,
  { obtain ⟨f, hf⟩ := this,
    refine ⟨f.prod, _⟩ ,
    have := unique_factorization_monoid.normalized_factors_prod ha,
    rw associated_eq_eq at this,
    rw [←this, ←multiset.prod_nsmul, ←hf] },
  refine multiset.exists_smul_of_dvd_count _ (λ x hx, _),
  have hxb := this x hx,
  convert dvd_mul_right p (fc.count x),
  rw [←multiset.count_nsmul, ←unique_factorization_monoid.normalized_factors_pow, ←h,
    unique_factorization_monoid.normalized_factors_mul ha hb],
  rw multiset.count_add,
  convert (add_zero _).symm,
  apply multiset.count_eq_zero_of_not_mem hxb,
end
