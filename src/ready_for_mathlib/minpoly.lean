import ready_for_mathlib.polynomial
import field_theory.minpoly

universes u v

variables {K : Type u} [field K] {R : Type v} [comm_ring R] [algebra K R]

open polynomial

open_locale polynomial

lemma minpoly_add_algebra_map {x : R} (hx : is_integral K x) (a : K) :
  minpoly K (x + (algebra_map K R a)) = (minpoly K x).comp (X - C a) :=
begin
  symmetry,
  refine minpoly.unique _ _ (monic_comp_X_sub_C (minpoly.monic hx) _) _ (λ q qmo hq, _),
  { simp [aeval_comp] },
  { have : (aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq,
    have H := minpoly.min K x (monic_comp_X_add_C qmo _) this,
    rw [degree_eq_nat_degree qmo.ne_zero, degree_eq_nat_degree
      (monic_comp_X_sub_C (minpoly.monic hx) _).ne_zero, with_bot.coe_le_coe, nat_degree_comp,
      nat_degree_X_sub_C, mul_one],
    rwa [degree_eq_nat_degree (minpoly.ne_zero hx), degree_eq_nat_degree
      (monic_comp_X_add_C qmo _).ne_zero, with_bot.coe_le_coe, nat_degree_comp,
      nat_degree_X_add_C, mul_one] at H }
end
