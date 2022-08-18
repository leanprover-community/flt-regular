import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.cyclotomic_units
import ring_theory.roots_of_unity
import number_theory.number_field
import number_theory.cyclotomic.zeta_sub_one_prime
import data.nat.prime_extras

variables {p : ℕ+} {K : Type*} [field K]
variables {ζ : K} (hζ : is_primitive_root ζ p)

open_locale big_operators non_zero_divisors number_field cyclotomic
open is_cyclotomic_extension number_field polynomial

local notation `RR` := 𝓞 K

--The whole file is now for a generic primitive root ζ, quite a lot of names should be changed.

--bunch of lemmas that should be stated more generally if we decide to go this way
lemma unit_coe (u : RRˣ) : (u : RR) * ((u⁻¹ : RRˣ) : RR) = 1 :=
begin
  norm_cast,
  simp only [mul_right_inv, units.coe_one],
end

lemma unit_coe_non_zero (u : RRˣ) : (u : K) ≠ 0 :=
begin
  by_contra h,
  have : (u : K) * ((u⁻¹ : RRˣ ) : K) = 1,
  { rw [coe_coe, coe_coe, ←subalgebra.coe_mul, ←units.coe_mul, mul_right_inv], refl },
  rw h at this,
  simp at this,
  exact this,
end

lemma coe_life (u : RRˣ) : ((u : RR) : K)⁻¹ = ((u⁻¹ : RRˣ) : RR) :=
begin
  rw [←coe_coe, ←coe_coe, inv_eq_one_div],
  symmetry,
  rw [eq_div_iff],
  { cases u with u₁ u₂ hmul hinv,
    simp only [units.inv_mk, coe_coe, units.coe_mk],
    rw [← mul_mem_class.coe_mul _ u₂, hinv, submonoid_class.coe_one] },
  { simp }
end

lemma auxil (a b c d : RRˣ) (h : a * b⁻¹ = c * d ) : a * d⁻¹ = b * c :=
begin
  rw mul_inv_eq_iff_eq_mul at *,
  rw h,
  apply symm,
  rw mul_assoc,
  rw mul_comm,
end

local attribute [instance] is_cyclotomic_extension.number_field
universe u
noncomputable theory

/-- zeta now as a unit in the ring of integers. This way there are no coe issues-/
@[simps {attrs := [`simp, `norm_cast]}] def is_primitive_root.unit' {p : ℕ+} {K : Type*}
  [field K] {ζ : K} (hζ : is_primitive_root ζ p) : (𝓞 K)ˣ :=
{ val := (⟨ζ, hζ.is_integral' ℤ p.pos⟩ : 𝓞 K),
  inv:= (⟨ζ⁻¹, hζ.inv'.is_integral' ℤ p.pos⟩ : 𝓞 K),
  val_inv := subtype.ext $ mul_inv_cancel $ hζ.ne_zero p.ne_zero,
  inv_val := subtype.ext $ inv_mul_cancel $ hζ.ne_zero p.ne_zero }

local notation `ζ1` := (hζ.unit' - 1 : 𝓞 K)
local notation `I` := ((ideal.span ({ζ1} : set (𝓞 K)) : ideal (𝓞 K)))

-- I don't know if this is so good: I've found the `simps` version (`coe_unit'_coe`) better.
-- Furthermore, this takes the name for the `is_primitive_root` one, which is super important.
-- This may be worth having with an obscure name for `norm_cast`.
--@[norm_cast] lemma is_primitive_root.unit'_coe : (hζ.unit' : K) = ζ := rfl

lemma is_primitive_root.unit'_zpow : hζ.unit' ^ (p : ℤ) = 1 :=
units.ext $ subtype.ext $ by simpa using hζ.pow_eq_one

lemma is_primitive_root.unit'_pow : hζ.unit' ^ (p : ℕ) = 1 :=
units.ext $ subtype.ext $ by simpa using hζ.pow_eq_one

lemma zeta_runity_pow_even (hpo : odd (p : ℕ)) (n : ℕ) : ∃ (m : ℕ),
  hζ.unit' ^ n = hζ.unit' ^ (2 * m) :=
begin
  rcases eq_or_ne n 0 with rfl | h,
  { use 0,
    simp only [mul_zero] },
  obtain ⟨r, hr⟩ := hpo,
  have he : 2 * (r + 1) * n = p * n + n, by {rw hr, ring},
  use (r + 1) * n,
  rw [←mul_assoc, he, pow_add],
  convert (one_mul _).symm,
  rw [pow_mul, hζ.unit'_pow, one_pow]
end

variables [number_field K]

lemma is_primitive_root.unit'_coe : is_primitive_root (hζ.unit' : RR) p :=
begin
 have z1 := hζ,
 have : (algebra_map RR K) (hζ.unit' : RR) = ζ := rfl,
 rw ← this at z1,
 exact z1.of_map_of_injective (is_fraction_ring.injective _ _),
end

variable (p)

/-- `is_gal_conj_real x` means that `x` is real. -/
def is_gal_conj_real (x : K) [is_cyclotomic_extension {p} ℚ K] : Prop := gal_conj K p x = x

variable {p}

lemma contains_two_primitive_roots {p q : ℕ} {x y : K} [finite_dimensional ℚ K]
  (hx : is_primitive_root x p) (hy : is_primitive_root y q) :
  (lcm p q ).totient ≤ (finite_dimensional.finrank ℚ K) :=
begin
  classical,
  let k := lcm p q,
  rcases nat.eq_zero_or_pos p with rfl | hppos,
  { simp },
  rcases nat.eq_zero_or_pos q with rfl | hqpos,
  { simp },
  let k := lcm p q,
  have hkpos : 0 < k := nat.pos_of_ne_zero (nat.lcm_ne_zero  hppos.ne' hqpos.ne'),
  set xu := is_unit.unit (hx.is_unit hppos) with hxu,
  let yu := is_unit.unit (hy.is_unit hqpos),
  have hxmem : xu ∈ roots_of_unity ⟨k, hkpos⟩ K,
  { rw [mem_roots_of_unity, pnat.mk_coe, ← units.coe_eq_one, units.coe_pow, is_unit.unit_spec],
    exact (hx.pow_eq_one_iff_dvd _).2 (dvd_lcm_left _ _) },
  have hymem : yu ∈ roots_of_unity ⟨k, hkpos⟩ K,
  { rw [mem_roots_of_unity, pnat.mk_coe, ← units.coe_eq_one, units.coe_pow, is_unit.unit_spec],
    exact (hy.pow_eq_one_iff_dvd _).2 (dvd_lcm_right _ _) },
  have hxuord : order_of (⟨xu, hxmem⟩ : roots_of_unity ⟨k, hkpos⟩ K) = p,
  { rw [← order_of_injective (roots_of_unity ⟨k, hkpos⟩ K).subtype subtype.coe_injective,
      subgroup.coe_subtype, subgroup.coe_mk, ← order_of_units, is_unit.unit_spec],
    exact hx.eq_order_of.symm },
  have hyuord : order_of (⟨yu, hymem⟩ : roots_of_unity ⟨k, hkpos⟩ K) = q,
  { rw [← order_of_injective (roots_of_unity ⟨k, hkpos⟩ K).subtype subtype.coe_injective,
      subgroup.coe_subtype, subgroup.coe_mk, ← order_of_units, is_unit.unit_spec],
    exact hy.eq_order_of.symm },
  obtain ⟨g : roots_of_unity ⟨k, hkpos⟩ K, hg⟩ := is_cyclic.exists_monoid_generator,
  obtain ⟨nx, hnx⟩ := hg ⟨xu, hxmem⟩,
  obtain ⟨ny, hny⟩ := hg ⟨yu, hymem⟩,
  obtain ⟨p₁, hp₁⟩ := dvd_lcm_left p q,
  obtain ⟨q₁, hq₁⟩ := dvd_lcm_left p q,
  have H : order_of g = k,
  { refine nat.dvd_antisymm (order_of_dvd_of_pow_eq_one _) (nat.lcm_dvd _ _),
    { have := (mem_roots_of_unity _ _).1 g.2,
      simp only [subtype.val_eq_coe, pnat.mk_coe] at this,
      exact_mod_cast this },
    { rw [← hxuord, ← hnx, order_of_pow],
      exact nat.div_dvd_of_dvd ((order_of g).gcd_dvd_left nx), },
    { rw [← hyuord, ← hny, order_of_pow],
      exact nat.div_dvd_of_dvd ((order_of g).gcd_dvd_left ny) } },
  have hroot := is_primitive_root.order_of g,
  rw [H, ← is_primitive_root.coe_submonoid_class_iff, ← is_primitive_root.coe_units_iff,
    ← coe_coe] at hroot,
  conv at hroot { congr, skip,
    rw [show k = (⟨k, hkpos⟩ : ℕ+), by simp] },
  haveI := is_primitive_root.adjoin_is_cyclotomic_extension ℚ hroot,
  convert submodule.finrank_le (algebra.adjoin ℚ ({g} : set K)).to_submodule,
  simpa using (is_cyclotomic_extension.finrank (algebra.adjoin ℚ ({g} : set K))
    (cyclotomic.irreducible_rat (pnat.pos ⟨k, hkpos⟩))).symm,
  all_goals { apply_instance }
end

lemma totient_le_one_dvd_two {a : ℕ} (han : 0 < a) (ha : a.totient ≤ 1) : a ∣ 2 :=
begin
 cases nat.totient_eq_one_iff.1 (show a.totient = 1, by linarith [nat.totient_pos han]) with h h;
  simp [h]
end

lemma eq_one_mod_one_sub {R} [comm_ring R] {t : R} :
  algebra_map R (R ⧸ ideal.span ({t - 1} : set R)) t = 1 :=
begin
  rw [←map_one $ algebra_map R $ R ⧸ ideal.span ({t - 1} : set R), ←sub_eq_zero, ←map_sub,
      ideal.quotient.algebra_map_eq, ideal.quotient.eq_zero_iff_mem],
  apply ideal.subset_span,
  exact set.mem_singleton _
end

lemma is_primitive_root.eq_one_mod_sub_of_pow {R} [comm_ring R] [is_domain R] {ζ : R}
  (hζ : is_primitive_root ζ p) {μ : R} (hμ : μ ^ (p : ℕ) = 1) :
  algebra_map R (R ⧸ ideal.span ({ζ - 1} : set R)) μ = 1 :=
begin
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ p.pos,
  rw [map_pow, eq_one_mod_one_sub, one_pow]
end

lemma aux {t} {l : 𝓞 K} {f : fin t → ℤ} {μ : K} (hμ : is_primitive_root μ p)
          (h : ∑ (x : fin t), f x • (⟨μ, hμ.is_integral p.pos⟩ : 𝓞 K) ^ (x : ℕ) = l) :
  algebra_map (𝓞 K) (𝓞 K ⧸ I) l = ∑ (x : fin t), f x :=
begin
  apply_fun algebra_map (𝓞 K) ((𝓞 K) ⧸ I) at h,
  simp only [map_sum, map_zsmul] at h,
  convert h.symm,
  funext x,
  convert (zsmul_one (f x)).symm,
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one p.pos,
  convert_to (1 : (𝓞 K) ⧸ I) ^ (x : ℕ) = 1,
  swap, { exact one_pow _ },
  rw [one_pow, hζ.unit'_coe.eq_one_mod_sub_of_pow], -- this file seriously needs tidying
  ext,
  push_cast,
  rw [subtype.coe_mk, ←pow_mul, ←pow_mul, ←mul_rotate', pow_mul, hζ.pow_eq_one, one_pow]
end

lemma is_primitive_root.p_mem_one_sub_zeta [hp : fact ((p : ℕ).prime)] :
  (p : 𝓞 K) ∈ I :=
begin
  classical,
  have key : _ = (p : 𝓞 K) := @@polynomial.eval_one_cyclotomic_prime _ hp,
  rw [cyclotomic_eq_prod_X_sub_primitive_roots hζ.unit'_coe, eval_prod] at key,
  simp only [eval_sub, eval_X, eval_C] at key,
  have : {↑hζ.unit'} ⊆ primitive_roots p (𝓞 K),
  { simpa using hζ.unit'_coe },
  rw [←finset.prod_sdiff this, finset.prod_singleton] at key,
  rw ←key,
  have := I .neg_mem_iff.mpr (ideal.subset_span (set.mem_singleton ζ1)),
  rw neg_sub at this,
  exact ideal.mul_mem_left _ _ this,
end

variable [is_cyclotomic_extension {p} ℚ K]

lemma roots_of_unity_in_cyclo_aux {x : K} {n l : ℕ}
  (hl : l ∈ n.divisors) (hx : x ∈ RR) (hhl : (cyclotomic l RR).is_root ⟨x, hx⟩)
  {ζ : K} (hζ : is_primitive_root ζ p) : l ∣ 2 * p :=
begin
by_contra,
  have hpl': is_primitive_root (⟨x, hx⟩ : RR) l,
    { rw is_root_cyclotomic_iff.symm,
      apply hhl,
      apply_instance,
      refine ⟨λ hzero, _⟩,
      rw [← subalgebra.coe_eq_zero] at hzero,
      simp only [subring_class.coe_nat_cast, nat.cast_eq_zero] at hzero,
      simpa [hzero] using hl },
  have hpl: is_primitive_root x l, by {have : (algebra_map RR K) (⟨x, hx⟩) = x, by{refl},
  have h4 := is_primitive_root.map_of_injective hpl', rw ← this,
  apply h4,
  apply is_fraction_ring.injective, },
  have KEY := contains_two_primitive_roots hpl hζ,
  have hirr : irreducible (cyclotomic p ℚ), by {exact cyclotomic.irreducible_rat p.prop},
  have hrank:= is_cyclotomic_extension.finrank K hirr,
  rw hrank at KEY,
  have pdivlcm : (p : ℕ) ∣ lcm l p := dvd_lcm_right l ↑p,
  cases pdivlcm,
  have ineq1 := nat.totient_super_multiplicative (p: ℕ) pdivlcm_w,
  rw ←pdivlcm_h at ineq1,
  have KEY3 := (mul_le_iff_le_one_right (nat.totient_pos p.prop)).mp (le_trans ineq1 KEY),
  have pdiv_ne_zero : 0 < pdivlcm_w, by {by_contra,
  simp only [not_lt, le_zero_iff] at h,
  rw h at pdivlcm_h,
  simp only [mul_zero, lcm_eq_zero_iff, pnat.ne_zero, or_false] at pdivlcm_h,
  apply absurd pdivlcm_h (ne_of_gt (nat.pos_of_mem_divisors hl)),},
  have K5 := (nat.dvd_prime nat.prime_two).1 (totient_le_one_dvd_two pdiv_ne_zero KEY3),
  cases K5,
  rw K5 at pdivlcm_h,
  simp only [mul_one] at pdivlcm_h,
  rw lcm_eq_right_iff at pdivlcm_h,
  have K6 : (p : ℕ) ∣ 2*(p : ℕ) := dvd_mul_left ↑p 2,
  apply absurd (dvd_trans pdivlcm_h K6) h,
  simp only [eq_self_iff_true, normalize_eq, pnat.coe_inj],
  rw K5 at pdivlcm_h,
  rw mul_comm at pdivlcm_h,
  have := dvd_lcm_left l (p : ℕ),
  simp_rw pdivlcm_h at this,
  apply absurd this h,
end

--do more generally
lemma roots_of_unity_in_cyclo (hpo : odd (p : ℕ)) (x : K)
  (h : ∃ (n : ℕ) (h : 0 < n), x^(n: ℕ) = 1) :
  ∃ (m : ℕ) (k : ℕ+), x = (-1) ^ (k : ℕ) * hζ.unit' ^ (m : ℕ) :=
begin
  obtain ⟨n, hn0, hn⟩ := h,
  have hx : x ∈ RR, by {rw mem_ring_of_integers,
  refine ⟨(X ^ n - 1),_⟩,
  split,
  { exact (monic_X_pow_sub_C 1 (ne_of_lt hn0).symm) },
  { simp only [hn, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self] },},
  have hxu : (⟨x, hx⟩ : RR)^n = 1, by {ext, simp only [submonoid_class.mk_pow, set_like.coe_mk,
    submonoid_class.coe_one], apply hn} ,
  have H: ∃ (m : ℕ) (k: ℕ+), (⟨x, hx⟩ : RR) = (-1)^(k : ℕ) * hζ.unit' ^ (m : ℕ),
  by {obtain ⟨l, hl, hhl⟩ := ((_root_.is_root_of_unity_iff hn0 _).1 hxu),
  have hlp := roots_of_unity_in_cyclo_aux hl hx hhl hζ,
  simp only [is_root.def] at hhl,
  have isPrimRoot : is_primitive_root (hζ.unit' : RR) p := hζ.unit'_coe,
  have hxl : (⟨x, hx⟩: RR)^l =1 , by {apply is_root_of_unity_of_root_cyclotomic _ hhl,
    simp only [nat.mem_divisors, dvd_refl, ne.def, true_and],
   apply (pos_iff_ne_zero.1 (nat.pos_of_mem_divisors hl))},
  have hxp' : (⟨x, hx⟩: RR) ^ (2* p : ℕ) = 1,
  { cases hlp,
    rw [hlp_h, pow_mul, hxl], simp only [one_pow] },
  have hxp'': (⟨x, hx⟩: RR)^(p : ℕ) = 1 ∨ (⟨x, hx⟩: RR)^(p : ℕ) = -1,
  by {rw mul_comm at hxp', rw pow_mul at hxp',
  apply eq_or_eq_neg_of_sq_eq_sq (⟨x, hx⟩^(p : ℕ) : RR) 1 _,
  simp only [submonoid_class.mk_pow, one_pow],
  apply hxp',},
  cases hxp'',
  obtain ⟨i, hi,Hi⟩ := (is_primitive_root.eq_pow_of_pow_eq_one isPrimRoot hxp'' p.prop),
  refine ⟨i, 2, _⟩,
  simp only [pnat.coe_bit0, pnat.one_coe, neg_one_sq, one_mul],
  apply Hi.symm,
  have hone : (-1 : RR)^(p : ℕ)= (-1 : RR), by {apply odd.neg_one_pow hpo,},
  have hxp3 : (-1 * ⟨x, hx⟩: RR)^( p : ℕ) = 1, by {rw [mul_pow, hone, hxp''],
  simp only [mul_neg, mul_one, neg_neg],},
  obtain ⟨i, hi,Hi⟩ := (is_primitive_root.eq_pow_of_pow_eq_one isPrimRoot hxp3 p.prop),
  refine ⟨i, 1, _⟩,
  simp_rw Hi,
  simp only [pnat.one_coe, pow_one, neg_mul, one_mul, neg_neg] },
  obtain ⟨m, k, hmk⟩ := H,
  refine ⟨m, k, _⟩,
  have eq : ((⟨x, hx⟩ : RR) : K) = x := rfl,
  rw [←eq, hmk],
  norm_cast,
  rw [subalgebra.coe_mul],
  congr' 1,
  { push_cast },
  { rw coe_coe,
    push_cast }
end

lemma fuck_norm_cast (h : p ≠ 2) : (p : ℕ) ≠ 2 :=
begin
  contrapose! h,
  exact pnat.coe_injective h
end

include hζ

lemma is_primitive_root.is_prime_one_sub_zeta [hp : fact ((p : ℕ).prime)] (h : p ≠ 2) :
  I .is_prime := -- this doesn't work without the space🤮
begin
  rw ideal.span_singleton_prime,
  { exact is_cyclotomic_extension.rat.zeta_sub_one_prime' hζ h },
  apply_fun (coe : (𝓞 K) → K),
  push_cast,
  rw [ne.def, sub_eq_zero],
  rintro rfl,
  exact hp.1.ne_one (hζ.unique is_primitive_root.one)
end

lemma is_primitive_root.two_not_mem_one_sub_zeta [hp : fact ((p : ℕ).prime)] (h : p ≠ 2) :
  (2 : 𝓞 K) ∉ I :=
begin
  have hpm := hζ.p_mem_one_sub_zeta,
  obtain ⟨k, hk⟩ := hp.1.odd (fuck_norm_cast h),
  apply_fun (coe : ℕ → 𝓞 K) at hk,
  rw [nat.cast_add, nat.cast_mul, nat.cast_two, nat.cast_one, ←coe_coe, add_comm] at hk,
  intro h2m,
  have := I .sub_mem hpm (I .mul_mem_right ↑k h2m),
  rw [sub_eq_of_eq_add hk] at this,
  exact (hζ.is_prime_one_sub_zeta h).ne_top (I .eq_top_of_is_unit_mem this is_unit_one)
end

omit hζ

lemma unit_inv_conj_not_neg_zeta_runity (h : p ≠ 2) (u : RRˣ) (n : ℕ) (hp : (p : ℕ).prime) :
  u * (unit_gal_conj K p u)⁻¹ ≠ -hζ.unit' ^ n :=
begin
  by_contra H,
  haveI := fact.mk hp,
  have hu := hζ.integral_power_basis'.basis.sum_repr u,
  set a := hζ.integral_power_basis'.basis.repr with ha,
  set φn := hζ.integral_power_basis'.dim with hφn,
  simp_rw [power_basis.basis_eq_pow, is_primitive_root.integral_power_basis'_gen] at hu,
  have hu' := congr_arg (int_gal ↑(gal_conj K p)) hu,
  replace hu' :
    (∑ (x : fin φn), (a u) x • (int_gal ↑(gal_conj K p)) (⟨ζ, hζ.is_integral p.pos⟩ ^ (x : ℕ))) =
    (unit_gal_conj K p u),
  { refine eq.trans _ hu',
    rw map_sum,
    congr' 1,
    ext x,
    congr' 1,
    rw map_zsmul },
  -- todo: probably swap `is_primitive_root.inv` and `is_primitive_root.inv'`.
  have : ∀ x : fin φn, int_gal ↑(gal_conj K p) (⟨ζ, hζ.is_integral p.pos⟩ ^ (x : ℕ)) =
                        ⟨ζ⁻¹, hζ.inv'.is_integral p.pos⟩ ^ (x : ℕ),
  { intro x,
    ext,
    simp only [int_gal_apply_coe, map_pow, subsemiring_class.coe_pow, subtype.coe_mk],
    rw [←map_pow, alg_equiv.coe_alg_hom, gal_conj_zeta_runity_pow hζ] },
    conv_lhs at hu' { congr, congr, funext, rw [this x] },
  set u' := (unit_gal_conj K p) u,
  replace hu := aux hζ hζ hu,
  replace hu' := aux hζ hζ.inv' hu', -- cool fact: `aux hζ _ hu'` works!
  rw mul_inv_eq_iff_eq_mul at H,
  -- subst H seems to be broken
  nth_rewrite 0 H at hu,
  push_cast at hu,
  rw [map_mul, map_neg, hζ.unit'_coe.eq_one_mod_sub_of_pow, neg_one_mul] at hu,
  swap,
  { rw [←pow_mul, mul_comm, pow_mul, hζ.unit'_coe.pow_eq_one, one_pow] },
  have key := hu'.trans hu.symm,
  have hI := hζ.is_prime_one_sub_zeta h,
  rw [←sub_eq_zero, sub_neg_eq_add, ←map_add, ←two_mul, ideal.quotient.algebra_map_eq,
      ideal.quotient.eq_zero_iff_mem, hI.mul_mem_iff_mem_or_mem] at key,
  cases key,
  { exact hζ.two_not_mem_one_sub_zeta h key },
  { exact hI.ne_top (I .eq_top_of_is_unit_mem key u'.is_unit) }
end

-- this proof has mild coe annoyances rn
lemma unit_inv_conj_is_root_of_unity (h : p ≠ 2) (hp : (p : ℕ).prime) (u : RRˣ) :
  ∃ m : ℕ, u * (unit_gal_conj K p u)⁻¹ = (hζ.unit' ^ m)^2 :=
begin
  have hpo : odd (p : ℕ) := hp.odd (fuck_norm_cast h),
  have := mem_roots_of_unity_of_abs_eq_one
    (u * (unit_gal_conj K p u)⁻¹ : K) _ _,
  have H := roots_of_unity_in_cyclo hζ hpo ((u * (unit_gal_conj K p u)⁻¹ : K)) this,
  obtain ⟨n, k, hz⟩ := H,
  simp_rw ← pow_mul,
  have hk := nat.even_or_odd k,
  cases hk,
  {simp only [hk.neg_one_pow, coe_coe, one_mul] at hz,
  simp_rw coe_life at hz,
  rw [←subalgebra.coe_mul, ←units.coe_mul, ←subalgebra.coe_pow, ←units.coe_pow] at hz,
  norm_cast at hz,
  rw hz,
  refine (exists_congr $ λ a, _).mp (zeta_runity_pow_even hζ hpo n),
  { rw mul_comm } },
  { by_contra hc,
    simp only [hk.neg_one_pow, coe_coe, neg_mul, one_mul] at hz,
    rw [coe_life, ← subalgebra.coe_mul, ← units.coe_mul, ← subalgebra.coe_pow,
      ← units.coe_pow] at hz,
    norm_cast at hz,
    simpa [hz] using unit_inv_conj_not_neg_zeta_runity hζ h u n hp },
  { exact unit_lemma_val_one K p u,},
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj K p u)⁻¹ : K) = (↑(unit_gal_conj K p u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simpa only [coe_coe, coe_life] },
end

lemma unit_lemma_gal_conj (h : p ≠ 2) (hp : (p : ℕ).prime) (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), (is_gal_conj_real p (x : K)) ∧ (u : K) = x * (hζ.unit' ^ n) :=
begin
  have := unit_inv_conj_is_root_of_unity hζ h hp u,
  obtain ⟨m, hm⟩ := this,
  let xuu:=u * (hζ.unit'⁻¹ ^ (m)),
  use [xuu, m],
   rw is_gal_conj_real,
  have hy : u * (hζ.unit' ^ m)⁻¹ = (unit_gal_conj K p u) * hζ.unit' ^ ( m),
  by {rw pow_two at hm,
  have := auxil u (unit_gal_conj K p u) (hζ.unit' ^ m) (hζ.unit' ^ m),
  apply this hm},
  dsimp,
  simp only [inv_pow, alg_hom.map_mul],
  have hz: gal_conj K p (hζ.unit' ^ m)⁻¹ =(hζ.unit' ^ m),
  { simp [gal_conj_zeta_runity_pow hζ] },
  rw ← coe_coe,
  rw ← coe_coe,
  split,
  rw (_ : (↑(hζ.unit' ^ m)⁻¹ : K) = (hζ.unit' ^ m : K)⁻¹),
  rw [map_mul, hz],
  have hzz := unit_gal_conj_spec K p u,
  simp only [coe_coe],
  rw hzz,
  rw [←subalgebra.coe_pow, ←units.coe_pow, ←subalgebra.coe_mul, ←units.coe_mul],
  rw ← hy,
  simp only [subalgebra.coe_pow, subalgebra.coe_eq_zero, mul_eq_mul_left_iff,
  units.ne_zero, or_false, subalgebra.coe_mul, units.coe_pow, units.coe_mul],
  rw ← coe_life,
  simp only [subalgebra.coe_pow, units.coe_pow],
  simp_rw ← inv_pow,
  simp only [inv_pow, coe_coe],
  rw ← coe_life,
  simp only [subalgebra.coe_pow, units.coe_pow],
  simp,
  rw [← coe_life, units.coe_pow],
  simp only [subalgebra.coe_pow, units.coe_pow, ← inv_pow],
  rw [mul_assoc, ←mul_pow, hζ.coe_unit'_coe, inv_mul_cancel (hζ.ne_zero p.ne_zero),
      one_pow, mul_one],
end

/-
lemma unit_lemma (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), element_is_real (x : KK) ∧ (u : KK) = x * (zeta_runity p ℚ) ^ n :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  { have : ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (zeta_runity p ℚ) ^ (2 * m),
    admit, --follows from above with some work
          -- what we have shows its +- a power of zeta_runity
    obtain ⟨m, hm⟩ := this,
    use [u * (zeta_runity p ℚ)⁻¹ ^ m, m],
    split,
    { rw element_is_real,
      intro φ,
      have := congr_arg (conj ∘ φ ∘ coe) hm,
      simp at this,
      simp [alg_hom.map_inv],
      rw ← coe_coe,
      rw ← coe_coe, -- TODO this is annoying
      rw (_ : (↑(zeta_runity p ℚ ^ m)⁻¹ : KK) = (zeta_runity p ℚ ^ m : KK)⁻¹),
      rw alg_hom.map_inv,
      rw ring_hom.map_inv,
      rw mul_inv_eq_iff_eq_mul₀,
      simp,
      admit, -- wow we should really have some more structure and simp lemmas to tame this beast
      admit, -- similar silly goal to below
      admit,
       },
    { simp only [mul_assoc, inv_pow, subalgebra.coe_mul, coe_coe, units.coe_mul, zpow_coe_nat],
      norm_cast,
      simp, }, },
  { exact unit_lemma_val_one p u, },
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj p u)⁻¹ : KK) = (↑(unit_gal_conj p u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simp,
    admit, -- tis a silly goal
     },
end
-/
