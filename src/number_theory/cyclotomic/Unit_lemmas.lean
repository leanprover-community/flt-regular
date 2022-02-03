import number_theory.cyclotomic.galois_action_on_cyclo

variables (p : ℕ+) (K : Type*) [field K]

open is_cyclotomic_extension
open cyclotomic_ring

local notation `KK` := cyclotomic_field p ℚ
local notation `RR` := number_field.ring_of_integers (cyclotomic_field p ℚ)
local notation `ζ` := zeta p ℚ KK

local attribute [instance] is_cyclotomic_extension.number_field

/-- `is_gal_conj_real x` means that `x` is real. -/
def is_gal_conj_real (x : KK) : Prop := gal_conj p x = x


--bunch of lemmas that should be stated more generally if we decide to go this way
lemma unit_coe (u : RRˣ) : (u : RR) * ((u⁻¹ : RRˣ) : RR) = 1 :=
begin
  norm_cast,
  simp only [mul_right_inv, units.coe_one],
end

lemma unit_coe_non_zero (u  : RRˣ) : (u : KK) ≠ 0 :=
begin
  by_contra h,
  have : (u : KK) * ((u⁻¹ : RRˣ ) : KK) = 1, by {simp,norm_cast, apply unit_coe,},
  rw h at this,
  simp at this,
  exact this,
end

lemma coe_life (u : RRˣ) : ((u : RR) : KK)⁻¹ = ((u⁻¹ : RRˣ) : RR) :=
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

lemma auxil (a b c d : RRˣ) (h : a * b⁻¹ = c * d ) : a * d⁻¹ = b * c :=
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

lemma zeta_runity_pow_even (h : 2 < p)  (n : ℕ) : ∃ (m : ℕ), (zeta_runity p ℚ KK)^n = (zeta_runity p ℚ KK)^(2*m) :=
begin
  sorry, --2 is invertible if `p≠ 2`.
end

lemma unit_inv_conj_not_neg_zeta_runity (h : 2 < p)  (u : RRˣ) (n  : ℕ) :
  u * (unit_gal_conj p u)⁻¹ ≠  -(zeta_runity p ℤ RR) ^ n :=
begin
  by_contra H,
  sorry,
end

-- this proof has mild coe annoyances rn
lemma unit_inv_conj_is_root_of_unity (h : 2 < p)  (u : RRˣ) :
  ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = ((zeta_runity p ℤ RR) ^ (m))^2 :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  have H:= roots_of_unity_in_cyclo p ((u * (unit_gal_conj p u)⁻¹ : KK)) this,
  obtain ⟨n, k, hz⟩ := H,
  simp_rw ← pow_mul,
  have hk := nat.even_or_odd k,
  cases hk,
  sorry; { simp [nat.neg_one_pow_of_even hk] at hz,
    simp_rw  coe_life at hz,
    norm_cast at hz,
    norm_cast,
    rw hz,
    have := zeta_runity_pow_even p h n,
    obtain ⟨m , Hm⟩ := this,
    use m,
    rw mul_comm,
    exact Hm},
  sorry; { by_contra hc,
    simp [nat.neg_one_pow_of_odd hk] at hz,
    simp_rw  coe_life at hz,
    norm_cast at hz,
    have := unit_inv_conj_not_neg_zeta_runity p h u n,
    rw hz at this,
    simp at this,
    exact this, },
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


lemma unit_lemma_gal_conj (h : 2 < p)  (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), (is_gal_conj_real p (x : KK)) ∧ (u : KK) = x * (zeta_runity p ℚ KK) ^ n :=

begin
  have := unit_inv_conj_is_root_of_unity p h u,
  obtain ⟨m, hm⟩ := this,
  use [u * (zeta_runity p ℚ KK)⁻¹ ^ (m), m],
  split,
  sorry; { rw is_gal_conj_real,
  have hy : u * ((zeta_runity p ℚ) ^ ( m))⁻¹ = (unit_gal_conj p u) *  (zeta_runity p ℚ) ^ ( m), by {
  rw pow_two at hm,
  have := auxil p u (unit_gal_conj p u)  ((zeta_runity p ℚ) ^ (m)) ((zeta_runity p ℚ) ^ (m)),
  apply this hm,},
  dsimp,
  simp only [inv_pow, alg_hom.map_mul],
  have hz: gal_conj p ((zeta_runity p ℚ)  ^ ( m))⁻¹ =(zeta_runity p ℚ)  ^ ( m) , by {simp, rw ← coe_coe,
  rw zeta_runity_coe,
  rw gal_conj_zeta_runity_coe,
  simp only [inv_pow₀, gal_conj_zeta_runity, inv_inv₀],},
  rw ← coe_coe,
  rw ← coe_coe,
  rw (_ : (↑(zeta_runity p ℚ ^ m)⁻¹ : KK) = (zeta_runity p ℚ ^ m : KK)⁻¹),
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
  all_goals{sorry} /- { simp only [exists_prop, inv_pow, zpow_coe_nat] at *,
  norm_cast,
  simp only [inv_mul_cancel_right] at * }, -/
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
