import number_theory.cyclotomic.galois_action_on_cyclo



variables (p : ℕ+)

open is_cyclotomic_extension
open cyclotomic_ring

local notation `KK` := cyclotomic_field p ℚ
local notation `RR` := number_field.ring_of_integers (cyclotomic_field p ℚ)
local notation `ζ` := zeta' p ℚ KK

/-- `is_gal_conj_real x` means that `x` is real. -/
def is_gal_conj_real (x : KK) : Prop := gal_conj p x = x


--bunch of lemmas that should be stated more generally if we decide to go this way
lemma unit_coe (u : units RR) : (u : RR) * ((u⁻¹ : units RR) : RR) = 1 :=
begin
norm_cast,
simp only [mul_right_inv, units.coe_one],
end

lemma unit_coe_non_zero (u  : units RR) : (u : KK) ≠ 0 :=
begin
 by_contra h,
 have : (u : KK) * ((u⁻¹ : units RR ) : KK) = 1, by {simp,norm_cast, apply unit_coe,},
 rw h at this,
 simp at this,
 exact this,
end

lemma coe_life (u : units RR) : ((u : RR) : KK)⁻¹ = ((u⁻¹ : units RR) : RR) :=
begin
  rw ← coe_coe,
  rw ← coe_coe,
  rw inv_eq_one_div,
  have hu:= unit_coe_non_zero p u,
  rw div_eq_iff hu,
  rw mul_comm,
  simp only [coe_coe],
  norm_cast,
  simp only [mul_right_inv, units.coe_one],
end

lemma auxil (a b c d : units RR) (h : a * b⁻¹ = c * d ) : a * d⁻¹ = b * c :=
begin
rw mul_inv_eq_iff_eq_mul at *,
rw h,
apply symm,
rw mul_assoc,
rw mul_comm,
end

--do more generally
lemma roots_of_unity_in_cyclo (x  : KK) (h : ∃ (n : ℕ) (h : 0 < n), x^(n: ℕ) =1 ) :
  ∃ (m k: ℕ+), x = (-1)^(k : ℕ) * ζ^(m : ℕ) :=
begin
sorry,
end

lemma zeta_pow_even (h : 2 < p)  (n : ℕ) : ∃ (m : ℕ), (zeta p ℚ)^n = (zeta p ℚ)^(2*m) :=
begin
  sorry, --2 is invertible if `p≠ 2`.
end

lemma unit_inv_conj_not_neg_zeta (h : 2 < p)  (u : units RR) (n  : ℕ) :
  u * (unit_gal_conj p u)⁻¹ ≠  -(zeta p ℚ) ^ n :=
begin
  by_contra H,
sorry,
end


lemma unit_inv_conj_is_root_of_unity (h : 2 < p)  (u : units RR) :
  ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = ((zeta p ℚ) ^ (m))^2 :=
begin
 have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
 have H:= roots_of_unity_in_cyclo p ((u * (unit_gal_conj p u)⁻¹ : KK)) this,
 rw ← zeta_coe at H,
 obtain ⟨n, k, hz⟩ := H,
 simp_rw ← pow_mul,
 have hk := nat.even_or_odd k,
 cases hk,
 {simp [nat.neg_one_pow_of_even hk] at hz,
 simp_rw  coe_life at hz,
 norm_cast at hz,
 rw hz,
 have := zeta_pow_even p h n,
 obtain ⟨m , Hm⟩ := this,
 use m,
 rw mul_comm,
 exact Hm},
 {by_contra hc,
 simp [nat.neg_one_pow_of_odd hk] at hz,
 simp_rw  coe_life at hz,
 norm_cast at hz,
 have := unit_inv_conj_not_neg_zeta p h u n,
 rw hz at this,
 simp at this,
 exact this,},
  { exact unit_lemma_val_one p u,},
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj p u)⁻¹ : KK) = (↑(unit_gal_conj p u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simp,
    rw coe_life,
    norm_cast,
    apply uni_gal_conj_inv,
     },
end


lemma unit_lemma_gal_conj (h : 2 < p)  (u : units RR) :
  ∃ (x : units RR) (n : ℤ), (is_gal_conj_real p (x : KK)) ∧ (u : KK) = x * (zeta p ℚ) ^ n :=

begin
  have := unit_inv_conj_is_root_of_unity p h u,
  obtain ⟨m, hm⟩ := this,
  use [u * (zeta p ℚ)⁻¹ ^ (m), m],
  split,
  { rw is_gal_conj_real,
  have hy : u * ((zeta p ℚ) ^ ( m))⁻¹ = (unit_gal_conj p u) *  (zeta p ℚ) ^ ( m), by {
  rw pow_two at hm,
  have := auxil p u (unit_gal_conj p u)  ((zeta p ℚ) ^ (m)) ((zeta p ℚ) ^ (m)),
  apply this hm,},
  dsimp,
  simp only [inv_pow, alg_hom.map_mul],
  have hz: gal_conj p ((zeta p ℚ)  ^ ( m))⁻¹ =(zeta p ℚ)  ^ ( m) , by {simp, rw ← coe_coe,
  rw zeta_coe,
  rw gal_conj_zeta_coe,
  simp only [inv_pow₀, gal_conj_zeta, inv_inv₀],},
  rw ← coe_coe,
  rw ← coe_coe,
  rw (_ : (↑(zeta p ℚ ^ m)⁻¹ : KK) = (zeta p ℚ ^ m : KK)⁻¹),
  rw hz,
  have hzz := unit_gal_conj_spec p u,
  rw hzz,
  simp only [coe_coe],
  norm_cast,
  rw ← hy,
  simp only [subalgebra.coe_pow, subalgebra.coe_eq_zero, mul_eq_mul_left_iff,
  units.ne_zero, or_false, subalgebra.coe_mul, units.coe_pow, units.coe_mul],
  rw ← coe_life,
  simp only [subalgebra.coe_pow, units.coe_pow],
  simp_rw ← inv_pow,
  simp only [inv_pow, coe_coe],
  rw ← coe_life,
  simp only [subalgebra.coe_pow, units.coe_pow],
  },
  dsimp at *,
  simp only [exists_prop, inv_pow, zpow_coe_nat] at *,
  norm_cast,
  simp only [inv_mul_cancel_right] at *,
end

/-
lemma unit_lemma (u : units RR) :
  ∃ (x : units RR) (n : ℤ), element_is_real (x : KK) ∧ (u : KK) = x * (zeta p ℚ) ^ n :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  { have : ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (zeta p ℚ) ^ (2 * m),
    sorry, --follows from above with some work
          -- what we have shows its +- a power of zeta
    obtain ⟨m, hm⟩ := this,
    use [u * (zeta p ℚ)⁻¹ ^ m, m],
    split,
    { rw element_is_real,
      intro φ,
      have := congr_arg (conj ∘ φ ∘ coe) hm,
      simp at this,
      simp [alg_hom.map_inv],
      rw ← coe_coe,
      rw ← coe_coe, -- TODO this is annoying
      rw (_ : (↑(zeta p ℚ ^ m)⁻¹ : KK) = (zeta p ℚ ^ m : KK)⁻¹),
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
