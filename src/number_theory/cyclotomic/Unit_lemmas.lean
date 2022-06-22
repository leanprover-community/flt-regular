import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.cyclotomic_units
import ring_theory.roots_of_unity
import number_theory.number_field
import ready_for_mathlib.totient_stuff
import z_basis

variables {p : ℕ+} {K : Type*} [field K]
variables {ζ : K} (hζ : is_primitive_root ζ p)

open_locale big_operators non_zero_divisors number_field pnat cyclotomic
open is_cyclotomic_extension
open cyclotomic_ring
open number_field polynomial

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
@[simps] def is_primitive_root.unit' {p : ℕ+} {K : Type*} [field K] {ζ : K}
  (hζ : is_primitive_root ζ p) : (𝓞 K)ˣ :=
{ val := (⟨ζ, hζ.is_integral' ℤ p.pos⟩ : 𝓞 K),
  inv:= (⟨ζ ^ ((p - 1): ℕ), subalgebra.pow_mem _ (hζ.is_integral' ℤ p.pos) _⟩ : 𝓞 K),
  val_inv :=
  begin
    ext1,
    dsimp at *,
    rw [pow_sub₀, hζ.pow_eq_one, pow_one, one_mul],
    apply mul_inv_cancel,
    any_goals { apply hζ.ne_zero p.ne_zero },
    exact pnat.one_le p
  end,
  inv_val:=
  begin
    ext1,
    dsimp at *,
    rw [pow_sub₀, hζ.pow_eq_one, pow_one, one_mul],
    apply inv_mul_cancel,
    any_goals { apply hζ.ne_zero p.ne_zero },
    exact pnat.one_le p
 end }

lemma is_primitive_root.unit'_coe : (hζ.unit' : K) = ζ := rfl

lemma is_primitive_root.unit_pow : hζ.unit' ^ (p : ℤ) = 1 :=
begin
simp_rw is_primitive_root.unit',
ext1,
ext1,
simp,
apply hζ.pow_eq_one,
end

lemma zeta_runity_pow_even (hpo : odd (p : ℕ)) (n : ℕ) : ∃ (m : ℕ),
  hζ.unit' ^ n = hζ.unit' ^ (2 * m) :=
begin
  by_cases n = 0,
  use 0,
  rw h,
  simp only [mul_zero],
  rw odd at hpo,
  obtain ⟨r, hr⟩ := hpo,
  have he : 2*(r+1)*n=p*n+n, by {rw hr, linarith,},
  use (r+1)*n,
  rw ←mul_assoc,
  simp_rw he,
  rw pow_add,
  have h1 : hζ.unit' ^ ((p : ℤ) * n) = 1,
  { rw [zpow_mul, hζ.unit_pow, one_zpow] },
  norm_cast at h1,
  simp_rw h1,
  simp only [one_mul],
end

variables [number_field K]

lemma is_primitive_root.unit'_coe_2 : is_primitive_root (hζ.unit' : RR) p :=
begin
 have z1 := hζ,
 have : (algebra_map RR K) (hζ.unit' : RR) = ζ := rfl,
 rw ← this at z1,
 apply is_primitive_root.of_map_of_injective z1,
 apply is_fraction_ring.injective,
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

variable [is_cyclotomic_extension {p} ℚ K]

-- please speed this up
-- is it faster now?
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
  have ineq1 := totient_super_multiplicative (p: ℕ) pdivlcm_w,
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
  have isPrimRoot : is_primitive_root (hζ.unit' : RR) p := hζ.unit'_coe_2,
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
  { simp only [units.coe_pow, subsemiring_class.coe_pow, coe_coe]}
end

lemma unit_inv_conj_not_neg_zeta_runity (h : 2 < p) (u : RRˣ) (n : ℕ) (hp : (p : ℕ).prime) :
  u * (unit_gal_conj K p u)⁻¹ ≠ -hζ.unit' ^ n :=
begin
  by_contra H,
  haveI := fact.mk hp,
  have hu := (rat.power_basis_int' hζ).basis.sum_repr u,
  set a := (rat.power_basis_int' hζ).basis.repr with ha,
  set φn := (rat.power_basis_int' hζ).dim with hφn,
  simp_rw [power_basis.basis_eq_pow, rat.power_basis_int'_gen] at hu,
  have hu' := congr_arg (int_gal (gal_conj K p)) hu,
  --⇑(int_gal (gal_conj K p)) ↑u
  replace hu' :
    (∑ (x : fin φn), (a u) x • (int_gal (gal_conj K p)) (⟨ζ, hζ.is_integral p.pos⟩ ^ (x : ℕ))) =
    (unit_gal_conj K p u),
  sorry { refine eq.trans _ hu',
    rw map_sum,
    congr' 1,
    ext x,
    congr' 1,
    rw map_zsmul },
  have : ∀ x, int_gal (gal_conj K p) (⟨ζ, hζ.is_integral p.pos⟩ ^ (x : ℕ)) =
              ⟨ζ, hζ.is_integral p.pos⟩ ^ ((p : ℕ) - x),
  { intro x,
    ext,
    simp only [int_gal_apply_coe, map_pow, subsemiring_class.coe_pow, subtype.coe_mk],
    rw [alg_hom.restrict_domain],
    simp only [alg_hom.coe_comp, alg_hom.coe_restrict_scalars', is_scalar_tower.coe_to_alg_hom',
               function.comp_app, gal_conj_zeta_runity, inv_pow],
    sorry
  },
  sorry,
end

-- this proof has mild coe annoyances rn
lemma unit_inv_conj_is_root_of_unity (h : 2 < p) (hpo : odd (p : ℕ)) (u : RRˣ) :
  ∃ m : ℕ, u * (unit_gal_conj K p u)⁻¹ = (hζ.unit' ^ m)^2 :=
begin
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
    simpa [hz] using unit_inv_conj_not_neg_zeta_runity hζ h u n },
  { exact unit_lemma_val_one K p u,},
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj K p u)⁻¹ : K) = (↑(unit_gal_conj K p u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simpa only [coe_coe, coe_life] },
end


lemma unit_lemma_gal_conj (h : 2 < p) (hpo : odd (p : ℕ)) (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), (is_gal_conj_real p (x : K)) ∧ (u : K) = x * (hζ.unit' ^ n) :=
begin
  have := unit_inv_conj_is_root_of_unity hζ h hpo u,
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
  have hz: gal_conj K p (hζ.unit' ^ m)⁻¹ =(hζ.unit' ^ m) := by simp,
  rw ← coe_coe,
  rw ← coe_coe,
  split,
  rw (_ : (↑(hζ.unit' ^ m)⁻¹ : K) = (hζ.unit' ^ m : K)⁻¹),
  rw hz,
  have hzz := unit_gal_conj_spec K p u,
  rw hzz,
  simp only [coe_coe],
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
  rw [mul_assoc, ← mul_pow, ← coe_coe hζ.unit', hζ.unit'_coe, inv_mul_cancel (hζ.ne_zero p.ne_zero),
    one_pow, mul_one],
end

/-
lemma unit_lemma (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), element_is_real (x : KK) ∧ (u : KK) = x * (zeta_runity p ℚ) ^ n :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  { have : ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (zeta_runity p ℚ) ^ (2 * m),
    sorry, --follows from above with some work
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
      sorry, -- wow we should really have some more structure and simp lemmas to tame this beast
      sorry, -- similar silly goal to below
      sorry,
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
    sorry, -- tis a silly goal
     },
end
-/
