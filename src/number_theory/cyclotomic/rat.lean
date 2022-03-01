import number_theory.cyclotomic.galois_action_on_cyclo

import ready_for_mathlib.zeta_sub_one
import ready_for_mathlib.integrally_closed
import ready_for_mathlib.eiseinstein

universes u

open finite_dimensional polynomial algebra

variables (n : ℕ+) (L : Type u) [field L] [char_zero L]

namespace is_cyclotomic_extension

namespace rat

namespace singleton

variables [is_cyclotomic_extension {n} ℚ L]

end singleton

end rat

namespace int

namespace singleton

open_locale number_field

local attribute [instance] is_cyclotomic_extension.number_field
local attribute [-instance] cyclotomic_field.algebra

lemma cyclotomic_ring.is_integral_closure_prime {p : ℕ+} [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) :
  is_integral_closure (cyclotomic_ring p ℤ ℚ) ℤ (cyclotomic_field p ℚ) :=
begin
  refine ⟨is_fraction_ring.injective _ _, λ x, ⟨λ h, ⟨⟨x, _⟩, rfl⟩, _⟩⟩,
  { haveI : is_cyclotomic_extension {p} ℚ (cyclotomic_field p ℚ),
    { convert cyclotomic_field.is_cyclotomic_extension p _,
      { apply subsingleton.elim (algebra_rat) _,
        exact algebra_rat_subsingleton },
      { exact ne_zero.char_zero } },
    let B := (zeta_primitive_root p ℚ (cyclotomic_field p ℚ)).sub_one_power_basis ℚ,
    have hζ := zeta_primitive_root p ℚ (cyclotomic_field p ℚ),
    have hint : is_integral ℤ B.gen :=  is_integral_sub (hζ.is_integral hp.out.pos) is_integral_one,
    have H := discr_mul_is_integral_mem_adjoin ℚ hint h,
    rw [discr_odd_prime' hζ hodd] at H,
    replace H : (p : ℤ) ^ ((p : ℕ) - 2) • x ∈ adjoin ℤ ({B.gen} : set (cyclotomic_field p ℚ)),
    { by_cases heven : even (((p : ℕ) - 1) / 2),
      { rw [nat.neg_one_pow_of_even heven, one_mul] at H,
        simp only [coe_coe] at H,
        simp only [coe_coe, zsmul_eq_mul, int.cast_pow, int.cast_coe_nat],
        convert H,
        simp },
      { rw [nat.neg_one_pow_of_odd (nat.odd_iff_not_even.2 heven)] at H,
        simp only [coe_coe, neg_mul, one_mul, neg_smul] at H,
        simp only [coe_coe, zsmul_eq_mul, int.cast_pow, int.cast_coe_nat],
        convert subalgebra.neg_mem _ H,
        rw [neg_neg],
        congr,
        simp } },
    have hmin : (minpoly ℤ B.gen).is_eisenstein_at (submodule.span ℤ {((p : ℕ) : ℤ)}),
    { have h₁ := minpoly.gcd_domain_eq_field_fractions ℚ hint,
      have h₂ := hζ.sub_one_minpoly_eq_cyclotomic_comp ℚ (cyclotomic.irreducible_rat hp.out.pos),
      rw [is_primitive_root.sub_one_power_basis_gen] at h₁,
      rw [h₁, ← map_cyclotomic_int, show int.cast_ring_hom ℚ = algebra_map ℤ ℚ, by refl,
        show ((X + 1)) = map (algebra_map ℤ ℚ) (X + 1), by simp, ← map_comp] at h₂,
      rw [is_primitive_root.sub_one_power_basis_gen, map_injective (algebra_map ℤ ℚ)
        ((algebra_map ℤ ℚ).injective_int) h₂],
      exact cyclotomic_comp_X_add_one_is_eisenstein_at },
    replace H := eiseinstein_integral_gen (nat.prime_iff_prime_int.1 hp.out) hmin hint h H,
    convert adjoin_le _ H,
    { exact subsingleton.elim _ _ },
    { exact subsingleton.elim _ _ },
    { simp only [is_primitive_root.sub_one_power_basis_gen, set.singleton_subset_iff,
        set_like.mem_coe],
      refine subalgebra.sub_mem _ (subset_adjoin _) (subalgebra.one_mem _),
      simp only [set.mem_set_of_eq, zeta_pow] } },
  { haveI : is_cyclotomic_extension {p} ℤ (cyclotomic_ring p ℤ ℚ),
    { convert cyclotomic_ring.is_cyclotomic_extension p ℤ ℚ,
      exact subsingleton.elim (algebra_int _) _ },
    rintro ⟨y, rfl⟩,
    exact is_integral.algebra_map ((is_cyclotomic_extension.integral {p} ℤ _) _) }
end

instance : is_integral_closure (cyclotomic_ring n ℤ ℚ) ℤ (cyclotomic_field n ℚ) := sorry

end singleton

end int

end is_cyclotomic_extension

section int_facts

noncomputable theory

open_locale number_field

local notation `KK` := cyclotomic_field n ℚ

local notation `RR` := 𝓞 (cyclotomic_field n ℚ)

--A.K.A theorem:FLT_facts 3
lemma flt_fact_3 [fact (n : ℕ).prime] (a : RR) :
  ∃ (m : ℤ), (a ^ (n : ℕ) - m) ∈ ideal.span ({n} : set RR) := sorry

open ideal is_cyclotomic_extension

-- TODO refactor add_pow_char_of_commute to use this instead of its own (basically the same) proof
-- TODO is the fact assumption necessary what if p is a prime power?
-- TODO other versions, e.g. one for sub and one for p^n with the
theorem add_pow_prime_eq_pow_add_pow_add_prime_mul_of_commute {R : Type*} [semiring R] (p : ℕ)
  [fact p.prime] (x y : R) (h : commute x y) : ∃ r : R, (x + y) ^ p = x ^ p + y ^ p + p * r :=
begin
  have : p = p - 1 + 1 := (nat.succ_pred_prime (fact.out _)).symm,
  rw [commute.add_pow h, finset.sum_range_succ_comm, tsub_self, pow_zero, nat.choose_self,
    nat.cast_one, mul_one, mul_one, this, finset.sum_range_succ'],
  simp only [this.symm, tsub_zero, mul_one, one_mul, nat.choose_zero_right, nat.cast_one, pow_zero],
  rw add_comm _ (y ^ p),
  simp_rw add_assoc,
  use (finset.range (p - 1)).sum
    (λ (x_1 : ℕ), x ^ (x_1 + 1) * y ^ (p - (x_1 + 1)) * ↑(p.choose (x_1 + 1) / p)),
  rw finset.mul_sum,
  congr' 2,
  apply finset.sum_congr rfl,
  intros i hi,
  rw [finset.mem_range] at hi,
  rw [nat.cast_comm, mul_assoc, mul_assoc, mul_assoc],
  congr,
  norm_cast,
  rw nat.div_mul_cancel,
  exact nat.prime.dvd_choose_self (nat.succ_pos _) (lt_tsub_iff_right.mp hi) (fact.out _),
end

theorem add_pow_prime_eq_pow_add_pow_add_prime_mul {R : Type*} [comm_semiring R] (p : ℕ)
  [fact p.prime] (x y : R) : ∃ r : R, (x + y) ^ p = x ^ p + y ^ p + p * r :=
add_pow_prime_eq_pow_add_pow_add_prime_mul_of_commute _ _ _ (commute.all _ _)

-- TODO can we make a relative version of this with another base ring instead of ℤ ?
-- A version of flt_facts_3 indep of the ring
lemma exists_int_sub_pow_prime_dvd {A : Type*} [comm_ring A] [is_cyclotomic_extension {n} ℤ A]
  [fact (n : ℕ).prime] (a : A) : ∃ (m : ℤ), (a ^ (n : ℕ) - m) ∈ span ({n} : set A) :=
begin
  have : a ∈ algebra.adjoin ℤ _ := @adjoin_roots {n} ℤ A _ _ _ _ a,
  apply algebra.adjoin_induction this,
  { intros x hx,
    rcases hx with ⟨hx_w, hx_m, hx_p⟩,
    simp only [set.mem_singleton_iff] at hx_m,
    rw [hx_m] at hx_p,
    simp only [hx_p, coe_coe],
    use 1,
    simp, },
  { intros r,
    use r ^ (n : ℕ),
    simp, },
  { rintros x y ⟨hx_m, hx_p⟩ ⟨hy_m, hy_p⟩,
    obtain ⟨r, hr⟩ := add_pow_prime_eq_pow_add_pow_add_prime_mul n x y,
    rw [hr],
    existsi hx_m + hy_m,
    push_cast,
    rw sub_add_eq_sub_sub, -- horrible calculation time
    rw sub_eq_add_neg,
    rw sub_eq_add_neg,
    rw add_comm _ (↑↑n * r),
    rw add_assoc,
    rw add_assoc,
    apply' ideal.add_mem _ _,
    sorry, -- TODO this is just a silly computation should be easy from here.
    rw mem_span_singleton, -- TODO probably a lemma
    sorry, -- hopefully easy?
   },
  { rintros x y ⟨hx_m, hx_p⟩ ⟨hy_m, hy_p⟩,
    rw mul_pow,
    simp,
    use hx_m * hy_m,
    sorry, -- TODO also shouldn't be too hard a calculation
  },
end

-- TODO I (alex) am not sure whether this is better as ideal span,
-- or fractional_ideal.span_singleton
/-- The principal ideal generated by `x + y ζ^i` for integer `x` and `y` -/
def flt_ideals (x y i : ℤ) : ideal RR :=
  ideal.span ({ x + y * ((zeta_runity n ℤ RR) ^ i : RRˣ) } : set RR)

variable {n} -- why does this not update (n : ℕ+)?

lemma mem_flt_ideals {x y i : ℤ} :
  (x : RR) + y * ((zeta_runity n ℤ RR) ^ i : RRˣ) ∈ flt_ideals n x y i :=
mem_span_singleton.mpr dvd_rfl

section to_move

variables {R : Type*} [semiring R] {s t : ideal R}

lemma ideal.add_left_subset  : s ≤ s + t := le_sup_left
lemma ideal.add_right_subset : t ≤ s + t := le_sup_right

variables {K : Type*} [semiring K]

lemma add_eq_mul_one_add_div {a : Kˣ} {b : K} : ↑a + b = a * (1 + ↑a⁻¹ * b) :=
by rwa [mul_add, mul_one, ← mul_assoc, units.mul_inv, one_mul]

end to_move

lemma flt_fact_2 {p : ℕ} [fact (p : ℕ).prime] (ph : 5 ≤ p) {x y z : ℤ} {i j : ℤ} (h : i ≠ j)
  (hp : is_coprime x y) (h : x ^ p + y ^ p = z ^ p) : flt_ideals n x y i + flt_ideals n x y j = ⊤ :=
begin
  let I := flt_ideals n x y i + flt_ideals n x y j,
  have : ∃ v : RRˣ, (v : RR) * y * (1 - (zeta_runity n ℤ RR)) ∈ I,
  { have := I.add_mem (ideal.add_left_subset $ mem_flt_ideals n)
                      (ideal.mul_mem_left _ (-1) $ ideal.add_right_subset $ mem_flt_ideals n),
    simp only [neg_mul, one_mul, neg_add_rev] at this,
    rw [neg_mul_eq_mul_neg, add_comm] at this,
    simp only [← add_assoc] at this,
    rw [add_assoc _ (-_) _, neg_add_self, add_zero, ←mul_add, add_comm, add_eq_mul_one_add_div,
        ←zpow_neg] at this,
    sorry
    -- I cannot get the tactic state to work here :/
  }, sorry,
end

end int_facts
