import ready_for_mathlib.polynomial
import field_theory.minpoly

universes u v

variables {K : Type u} [field K] {R : Type v} [comm_ring R] [is_domain R] [algebra K R]

open polynomial

open_locale polynomial

lemma sub_one_minpoly_eq_cyclotomic_of_irreducible {x : R} (hμ : is_integral R x) (a : K) :
  minpoly K (x + (algebra_map K R a)) = (minpoly K x).comp (X - C a) :=
begin
  have monicp : ∀ (q : K[X]), q.monic → (q.comp (X + 1)).monic,
  { intros q hq,
    refine monic_comp hq (monic_X_add_C _) (λ ha, _),
    have : ((X + 1 : K[X]) = X + C 1) := by simp,
    rw [this, nat_degree_X_add_C] at ha,
    exact one_ne_zero ha },
  have monicm : ∀ (q : K[X]), q.monic → (q.comp (X - 1)).monic,
  { intros q hq,
    refine monic_comp hq (monic_X_sub_C _) (λ ha, _),
    have : ((X - 1 : K[X]) = X - C 1) := by simp,
    rw [this, nat_degree_X_sub_C] at ha,
    exact one_ne_zero ha },
  symmetry,
  refine minpoly.unique _ _ (monicp _ (cyclotomic.monic _ _)) _ (λ q qmo hq, _),
  { rw [minpoly_eq_cyclotomic_of_irreducible hμ h],
    simp [aeval_comp] },
  { have : (aeval μ) (q.comp (X - 1)) = 0 := by simpa [aeval_comp] using hq,
    have H := minpoly.min K μ (monicm _ qmo) this,
    rw [degree_eq_nat_degree qmo.ne_zero, degree_eq_nat_degree
      (monicp _ (cyclotomic.monic _ _)).ne_zero, with_bot.coe_le_coe],
    rw [degree_eq_nat_degree (minpoly.ne_zero _)] at H,
    swap,
    apply_instance,
    swap,
    {
      refine hμ.is_integral _,
    }
       }
end
