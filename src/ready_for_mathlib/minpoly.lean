import field_theory.minpoly

namespace minpoly

open_locale polynomial

open polynomial

lemma gcd_domain_eq_field_fractions' {R A : Type*} (K L : Type*) [comm_ring R] [is_domain R]
  [normalized_gcd_monoid R] [field K] [comm_ring A] [is_domain A] [algebra R K]
  [is_fraction_ring R K] [algebra R A] {x : A} (hx : is_integral R x)
  [field L] [algebra A L] [algebra K L] [algebra R L] [is_scalar_tower R K L]
  [is_scalar_tower R A L] :
  minpoly K (algebra_map A L x) = (minpoly R x).map (algebra_map R K) :=
begin
  symmetry,
  refine eq_of_irreducible_of_monic _ _ _,
  { exact (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map
      (polynomial.monic.is_primitive (monic hx))).1 (irreducible hx) },
   { rw [aeval_map, aeval_def, is_scalar_tower.algebra_map_eq R A L, ← eval₂_map, eval₂_at_apply,
      eval_map, ← aeval_def, aeval, map_zero] },
  { exact (monic hx).map _ }
end

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. -/
lemma gcd_domain_dvd' {R A : Type*} [comm_ring R] [is_domain R] [normalized_gcd_monoid R]
  [comm_ring A] [is_domain A] [algebra R A] {x : A} (hx : is_integral R x)
  (hinj : function.injective (algebra_map R A)) {P : R[X]} (hP : P ≠ 0)
  (hroot : polynomial.aeval x P = 0) : minpoly R x ∣ P :=
begin
  let K := fraction_ring R,
  let L := fraction_ring A,
  haveI : no_zero_smul_divisors R L,
  { refine no_zero_smul_divisors.iff_algebra_map_injective.2 _,
    rw [is_scalar_tower.algebra_map_eq R A L],
    refine (is_fraction_ring.injective A L).comp hinj },
  let P₁ := P.prim_part,
  suffices : minpoly R x ∣ P₁,
  { exact dvd_trans this (prim_part_dvd _) },
  have hP₁ : polynomial.aeval x P₁ = 0,
  { rw [eq_C_content_mul_prim_part P, map_mul, aeval_C] at hroot,
    have hcont : P.content ≠ 0 := λ h, hP (content_eq_zero_iff.1 h),
    replace hcont := function.injective.ne hinj hcont,
    rw [map_zero] at hcont,
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hroot },
  apply (is_primitive.dvd_iff_fraction_map_dvd_fraction_map K (monic hx).is_primitive
    P.is_primitive_prim_part).2,
  let y := algebra_map A L x,
  have hy : is_integral R y := hx.algebra_map,
  rw [← gcd_domain_eq_field_fractions' K L hx],
  refine dvd _ _ _,
  rw [aeval_map, aeval_def, is_scalar_tower.algebra_map_eq R A L, ← eval₂_map, eval₂_at_apply,
    eval_map, ← aeval_def, hP₁, map_zero]
end

lemma degree_le_of_ne_zero_gcd {R A : Type*} [comm_ring R] [is_domain R] [normalized_gcd_monoid R]
  [comm_ring A] [is_domain A] [algebra R A] {x : A} (hx : is_integral R x)
  (hinj : function.injective (algebra_map R A))
  {p : R[X]} (hp0 : p ≠ 0) (hp : polynomial.aeval x p = 0) :
  degree (minpoly R x) ≤ degree p :=
begin
  rw [degree_eq_nat_degree (minpoly.ne_zero hx), degree_eq_nat_degree hp0],
  norm_cast,
  exact nat_degree_le_of_dvd (gcd_domain_dvd' hx hinj hp0 hp) hp0
end

lemma gcd_domain_unique {R A : Type*} [comm_ring R] [is_domain R] [normalized_gcd_monoid R]
  [comm_ring A] [is_domain A] [algebra R A] {x : A}
  (hinj : function.injective (algebra_map R A)) {P : R[X]} (hmo : P.monic)
  (hP : polynomial.aeval x P = 0)
  (Pmin : ∀ Q : R[X], Q.monic → polynomial.aeval x Q = 0 → degree P ≤ degree Q)
  (hroot : polynomial.aeval x P = 0) : P = minpoly R x :=
begin
  have hx : is_integral R x := ⟨P, hmo, hP⟩,
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := degree_le_of_ne_zero_gcd hx hinj hnz (by simp [hP]),
  contrapose! this,
  refine degree_sub_lt _ (ne_zero hx) _,
  { exact le_antisymm (min R x hmo hP)
      (Pmin (minpoly R x) (monic hx) (aeval R x)) },
  { rw [(monic hx).leading_coeff, hmo.leading_coeff] }
end

end minpoly
