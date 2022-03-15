import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.cyclotomic_units

variables (p : ℕ+) (K : Type*) [field K]


open_locale big_operators non_zero_divisors number_field pnat
open is_cyclotomic_extension
open cyclotomic_ring
open number_field polynomial

local notation `KK` := cyclotomic_field p ℚ
local notation `RR` := 𝓞 (cyclotomic_field p ℚ)
local notation `ζ` := zeta p ℚ KK

local attribute [instance] is_cyclotomic_extension.number_field

noncomputable theory

-- we're nearly here!

instance ℚ_cycl_ext : is_cyclotomic_extension {p} ℚ (cyclotomic_field p ℚ) := sorry

instance : has_pow KK ℕ:=infer_instance

/-- zeta now as a unit in the ring of integers. This way there are no coe issues-/
def zeta_unit' : RRˣ :={
val:= (⟨zeta p ℚ KK, zeta_integral p ℚ⟩ : RR),
inv:= (⟨(zeta p ℚ KK)^((p-1): ℕ), zeta_integral' p ℚ (p-1)⟩ : RR),
val_inv := by { have:= zeta_pow p ℚ KK ,
  have h1:= zeta_primitive_root p ℚ KK, have h2:= h1.is_unit p.2, have h3:=h2.ne_zero,
 tidy, rw  pow_sub₀, rw this, simp, apply mul_inv_cancel, apply h3, apply h3, linarith,},
inv_val:= by{have:= zeta_pow p ℚ KK ,
  have h1:= zeta_primitive_root p ℚ KK, have h2:= h1.is_unit p.2, have h3:=h2.ne_zero,
 tidy, rw  pow_sub₀, rw this, simp, apply inv_mul_cancel, apply h3, apply h3, linarith,} ,}

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
  ∃ (m k: ℕ+), x = (-1)^(k : ℕ) * (ζ')^(m : ℕ) :=
begin
  obtain ⟨n, hn0, hn⟩ := h,
  have hx : x ∈ RR, by {sorry,},
  have hy: ∃ (y : RRˣ), x = y, by {sorry},
  have hxu : (⟨x, hx⟩ : RR)^n = 1, by {ext, simp, apply hn,} ,
  obtain ⟨y, hyy⟩:= hy,
  rw hyy,
  have H: ∃ (m k: ℕ+), y = (-1)^(k : ℕ) * (ζ')^(m : ℕ), by {
  rw (_root_.is_root_of_unity_iff hn0) at hxu,
  obtain ⟨l, hl, hhl⟩:=hxu,
  simp at hhl,
  simp at hl,
  by_cases hlp: l ∣ p,
  cases hlp,
    sorry,
    sorry,},

  sorry,
end

lemma zeta_runity_pow_even (h : 2 < p) (n : ℕ) : ∃ (m : ℕ),
  (ζ')^n = (ζ')^(2*m) :=
begin
  by_cases  n = 0,
  use 0,
  rw h,
  simp,
  have r:= ((2 : zmod p)⁻¹).val,
  have hr: ∃ (k : ℕ), 2*r =1+p*k ,by { sorry,},
  use r*n,
  obtain ⟨k,hk⟩:= hr,
  rw ← mul_assoc,
  simp_rw hk,
  ring_exp,
  rw pow_add,
  have h1 : (zeta_unit' p)^ ((p : ℤ) * k * n) = 1,
  by {have:= zeta_unit_pow p, rw mul_assoc, simp_rw zpow_mul, simp_rw this, simp,},
  norm_cast at h1,
  rw ← mul_assoc,
  simp_rw h1,
  simp,
end


lemma unit_inv_conj_not_neg_zeta_runity (h : 2 < p)  (u : RRˣ) (n  : ℕ) :
  u * (unit_gal_conj p u)⁻¹ ≠  -(ζ') ^ n :=
begin
  by_contra H,
  sorry,
end

-- this proof has mild coe annoyances rn
lemma unit_inv_conj_is_root_of_unity (h : 2 < p)  (u : RRˣ) :
  ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (ζ' ^ (m))^2 :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  have H:= roots_of_unity_in_cyclo p ((u * (unit_gal_conj p u)⁻¹ : KK)) this,
  obtain ⟨n, k, hz⟩ := H,
  simp_rw ← pow_mul,
  have hk := nat.even_or_odd k,
  cases hk,
  simp [nat.neg_one_pow_of_even hk] at hz,
  simp_rw  coe_life at hz,
  norm_cast at hz,
  rw hz,
  have := zeta_runity_pow_even p h n,
  obtain ⟨m , Hm⟩ := this,
  use m,
  rw mul_comm,
  exact Hm,
  by_contra hc,
    simp [nat.neg_one_pow_of_odd hk] at hz,
    simp_rw  coe_life at hz,
    norm_cast at hz,
    have := unit_inv_conj_not_neg_zeta_runity p h u n,
    rw hz at this,
    simp at this,
    exact this,
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
  ∃ (x : RRˣ) (n : ℤ), (is_gal_conj_real p (x : KK)) ∧ (u : KK) = x * (ζ' ^ n) :=

begin
  have := unit_inv_conj_is_root_of_unity p h u,
  obtain ⟨m, hm⟩ := this,
  let xuu:=u * ((ζ')⁻¹ ^ (m)),
  use [xuu, m],
   rw is_gal_conj_real,
  have hy : u * (ζ'  ^ ( m))⁻¹ = (unit_gal_conj p u) *  ζ'  ^ ( m),
  by {rw pow_two at hm,
  have := auxil p u (unit_gal_conj p u)  (ζ'  ^ (m)) (ζ'  ^ (m)),
  apply this hm},
  dsimp,
  simp only [inv_pow, alg_hom.map_mul],
  have hz: gal_conj p (ζ'^ ( m))⁻¹ =(ζ'  ^ ( m)) ,
  by {simp_rw zeta_unit', simp},
  rw ← coe_coe,
  rw ← coe_coe,
  split,
  rw (_ : (↑(ζ' ^ m)⁻¹ : KK) = (ζ' ^ m : KK)⁻¹),
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
  simp,
  norm_cast,
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
