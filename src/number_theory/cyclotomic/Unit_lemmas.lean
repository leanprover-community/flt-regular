import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.cyclotomic_units
import ring_theory.roots_of_unity
import number_theory.number_field

variables (p : ℕ+) (K : Type*) [field K] [algebra ℚ K]


open_locale big_operators non_zero_divisors number_field pnat
open is_cyclotomic_extension
open cyclotomic_ring
open number_field polynomial

local notation `KK` := cyclotomic_field p ℚ
local notation `RR` := 𝓞 (cyclotomic_field p ℚ)
local notation `ζ` := zeta p ℚ KK

local attribute [instance] is_cyclotomic_extension.number_field

noncomputable theory

/-- zeta now as a unit in the ring of integers. This way there are no coe issues-/
def zeta_unit' : RRˣ :={
val:= (⟨zeta p ℚ KK, zeta_integral p ℚ⟩ : RR),
inv:= (⟨(zeta p ℚ KK)^((p-1): ℕ), zeta_integral' p ℚ (p-1)⟩ : RR),
val_inv := by { have:= zeta_pow p ℚ KK ,
  have h1:= zeta_primitive_root p ℚ KK, have h2:= h1.is_unit p.2, have h3:=h2.ne_zero,
 cases h2, cases p, dsimp at *, ext1, dsimp at *, rw pow_sub₀, rw this, simp,
 apply mul_inv_cancel, apply h3, apply h3, linarith,},
inv_val:= by{have:= zeta_pow p ℚ KK ,
  have h1:= zeta_primitive_root p ℚ KK, have h2:= h1.is_unit p.2, have h3:=h2.ne_zero,
 cases h2, cases p, dsimp at *, ext1, dsimp at *, rw pow_sub₀, rw this, simp,
 apply inv_mul_cancel, apply h3, apply h3, linarith,} ,}

local notation `ζ'`:= zeta_unit' p

lemma zeta_unit_coe: (ζ' : KK) = ζ :=by refl

lemma zeta_unit_pow : (ζ')^(p : ℤ) = 1 :=
begin
simp_rw zeta_unit',
ext1,
ext1,
simp,
apply zeta_pow,
end

lemma zeta_unit_coe_2 : is_primitive_root (ζ' : RR) p :=
begin
 have z1 := zeta_primitive_root p ℚ KK,
 have : (algebra_map RR KK) ((ζ' : RR)) = ζ, by{refl, },
 rw ← this at z1,
 apply is_primitive_root.of_map_of_injective z1,
 apply is_fraction_ring.injective,
end


/-- `is_gal_conj_real x` means that `x` is real. -/
def is_gal_conj_real (x : KK) : Prop := gal_conj p x = x

--bunch of lemmas that should be stated more generally if we decide to go this way
lemma unit_coe (u : RRˣ) : (u : RR) * ((u⁻¹ : RRˣ) : RR) = 1 :=
begin
  norm_cast,
  simp only [mul_right_inv, units.coe_one],
end

lemma unit_coe_non_zero (u : RRˣ) : (u : KK) ≠ 0 :=
begin
  by_contra h,
  have : (u : KK) * ((u⁻¹ : RRˣ ) : KK) = 1,
  { rw [coe_coe, coe_coe, ←subalgebra.coe_mul, ←units.coe_mul, mul_right_inv], refl },
  rw h at this,
  simp at this,
  exact this,
end

lemma coe_life (u : RRˣ) : ((u : RR) : KK)⁻¹ = ((u⁻¹ : RRˣ) : RR) :=
begin
  have hu:= unit_coe_non_zero p u,
  rw [←coe_coe, ←coe_coe, inv_eq_one_div, div_eq_iff hu, coe_coe, coe_coe,
      ←subalgebra.coe_mul, ←units.coe_mul, mul_left_inv], refl
end

lemma auxil (a b c d : RRˣ) (h : a * b⁻¹ = c * d ) : a * d⁻¹ = b * c :=
begin
  rw mul_inv_eq_iff_eq_mul at *,
  rw h,
  apply symm,
  rw mul_assoc,
  rw mul_comm,
end

lemma contains_two_primitive_roots (p q : ℕ)
(x y : K) (hx : is_primitive_root x p) (hy : is_primitive_root y q): (lcm p q ).totient ≤
(finite_dimensional.finrank ℚ K) :=
begin

sorry,
end

lemma totient_super_multiplicative (a b : ℕ) : a.totient * b.totient ≤ (a * b).totient :=
begin

sorry,
end

lemma totient_le_one_dvd_two {a : ℕ} (han : 0 < a) (ha : a.totient ≤ 1) : a ∣ 2 :=
begin
--totient_eq_one_iff
sorry,
end

-- please speed this up
-- is it faster now?
lemma roots_of_unity_in_cyclo_aux (x : KK) (n l : ℕ) (hn0 : 0 < n) (hl : l ∈ n.divisors)
(hx : x ∈ RR) (hxu : (⟨x, hx⟩ : RR)^n = 1 )
(hhl : (cyclotomic l {x // x ∈ 𝓞 (cyclotomic_field p ℚ)}).is_root ⟨x, hx⟩) : l ∣ 2 * p :=
begin
by_contra,
  have hpl': is_primitive_root (⟨x, hx⟩ : RR) l, by {rw is_root_cyclotomic_iff.symm, apply hhl,
  apply_instance,
  fsplit,
  rw nat.cast_ne_zero,
  apply (ne_of_gt (nat.pos_of_mem_divisors hl)),},
  have hpl: is_primitive_root x l, by {have : (algebra_map RR KK) (⟨x, hx⟩) = x, by{refl},
  have h4 := is_primitive_root.map_of_injective hpl', rw ← this,
  apply h4,
  apply is_fraction_ring.injective, },
  have hpp: is_primitive_root (ζ' : KK) p, by { rw zeta_unit_coe, apply zeta_primitive_root,},
  have KEY := contains_two_primitive_roots KK l p x ζ' hpl hpp,
  have hirr : irreducible (cyclotomic p ℚ), by {exact cyclotomic.irreducible_rat p.prop},
  have hrank:= is_cyclotomic_extension.finrank KK hirr,
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
lemma roots_of_unity_in_cyclo (hpo : odd (p : ℕ)) (x : KK)
  (h : ∃ (n : ℕ) (h : 0 < n), x^(n: ℕ) = 1) :
  ∃ (m : ℕ) (k : ℕ+), x = (-1)^(k : ℕ) * (ζ')^(m : ℕ) :=
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
  have H: ∃ (m : ℕ) (k: ℕ+), (⟨x, hx⟩ : RR) = (-1)^(k : ℕ) * (ζ')^(m : ℕ),
  by {obtain ⟨l, hl, hhl⟩ := ((_root_.is_root_of_unity_iff hn0 _).1 hxu),
  have hlp := roots_of_unity_in_cyclo_aux p x n l hn0 hl hx hxu hhl,
  simp only [is_root.def] at hhl,
  have isPrimRoot : is_primitive_root (ζ' : RR) p, by {apply zeta_unit_coe_2},
  have hxl : (⟨x, hx⟩: RR)^l =1 , by {apply is_root_of_unity_of_root_cyclotomic _ hhl,
    simp only [nat.mem_divisors, dvd_refl, ne.def, true_and],
   apply (pos_iff_ne_zero.1 (nat.pos_of_mem_divisors hl))},
  have hxp' : (⟨x, hx⟩: RR)^(2* p : ℕ) = 1 , by {cases hlp,
  rw [hlp_h, pow_mul, hxl], simp only [one_pow],},
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
  simp only [pnat.one_coe, pow_one, neg_mul, one_mul, neg_neg],},
  obtain ⟨m, k, hmk⟩ := H,
  refine ⟨m, k, _⟩,
  have eq : ((⟨x, hx⟩ : RR) : KK) = x := rfl,
  rw [←eq, hmk],
  norm_cast,
  rw [subalgebra.coe_mul],
  congr' 1,
  { push_cast },
  { simp only [units.coe_pow, subsemiring_class.coe_pow, coe_coe]}
end

lemma zeta_runity_pow_even (hpo : odd (p : ℕ)) (n : ℕ) : ∃ (m : ℕ),
  (ζ')^n = (ζ')^(2*m) :=
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
  have h1 : (zeta_unit' p)^ ((p : ℤ) * n) = 1,
  by {have:= zeta_unit_pow p, simp_rw zpow_mul, simp_rw this, simp only [one_zpow],},
  norm_cast at h1,
  simp_rw h1,
  simp only [one_mul],
end


lemma unit_inv_conj_not_neg_zeta_runity (h : 2 < p) (u : RRˣ) (n : ℕ) :
  u * (unit_gal_conj p u)⁻¹ ≠ -(ζ') ^ n :=
begin
  by_contra H,
  sorry,
end

-- this proof has mild coe annoyances rn
lemma unit_inv_conj_is_root_of_unity (h : 2 < p) (hpo : odd (p : ℕ)) (u : RRˣ) :
  ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (ζ' ^ (m))^2 :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  have H:= roots_of_unity_in_cyclo p hpo ((u * (unit_gal_conj p u)⁻¹ : KK)) this,
  obtain ⟨n, k, hz⟩ := H,
  simp_rw ← pow_mul,
  have hk := nat.even_or_odd k,
  cases hk,
  {simp only [hk.neg_one_pow, coe_coe, one_mul] at hz,
  simp_rw coe_life at hz,
  rw [←subalgebra.coe_mul, ←units.coe_mul, ←subalgebra.coe_pow, ←units.coe_pow] at hz,
  norm_cast at hz,
  rw hz,
  refine (exists_congr $ λ a, _).mp (zeta_runity_pow_even p hpo n),
  { rw mul_comm } },
  { by_contra hc,
    simp [hk.neg_one_pow] at hz,
    simp_rw coe_life at hz,
    rw [←subalgebra.coe_mul, ←units.coe_mul, ←subalgebra.coe_pow, ←units.coe_pow] at hz,
    norm_cast at hz,
    simpa [hz] using unit_inv_conj_not_neg_zeta_runity p h u n },
  { exact unit_lemma_val_one p u,},
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj p u)⁻¹ : KK) = (↑(unit_gal_conj p u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simp,
    rw coe_life,
    norm_cast,
    apply uni_gal_conj_inv, },
end


lemma unit_lemma_gal_conj (h : 2 < p) (hpo : odd (p : ℕ)) (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), (is_gal_conj_real p (x : KK)) ∧ (u : KK) = x * (ζ' ^ n) :=

begin
  have := unit_inv_conj_is_root_of_unity p h hpo u,
  obtain ⟨m, hm⟩ := this,
  let xuu:=u * ((ζ')⁻¹ ^ (m)),
  use [xuu, m],
   rw is_gal_conj_real,
  have hy : u * (ζ' ^ ( m))⁻¹ = (unit_gal_conj p u) * ζ' ^ ( m),
  by {rw pow_two at hm,
  have := auxil p u (unit_gal_conj p u) (ζ' ^ (m)) (ζ' ^ (m)),
  apply this hm},
  dsimp,
  simp only [inv_pow, alg_hom.map_mul],
  have hz: gal_conj p (ζ'^ ( m))⁻¹ =(ζ' ^ ( m)) ,
  by {simp_rw zeta_unit', simp},
  rw ← coe_coe,
  rw ← coe_coe,
  split,
  rw (_ : (↑(ζ' ^ m)⁻¹ : KK) = (ζ' ^ m : KK)⁻¹),
  rw hz,
  have hzz := unit_gal_conj_spec p u,
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
  norm_cast,
  rw [mul_assoc, ←subalgebra.coe_mul, units.inv_mul],
  simp,
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
