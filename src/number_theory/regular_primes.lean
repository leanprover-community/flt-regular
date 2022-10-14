
import field_theory.splitting_field
import number_theory.bernoulli
import number_theory.class_number.finite
import number_theory.class_number.admissible_abs
import number_theory.cyclotomic.cycl_rat
import number_theory.cyclotomic.rat


/-!
# Regular primes

## Main definitions

* `is_regular_number`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/


noncomputable theory
open nat polynomial

open number_field
open_locale classical number_field

section safe_instances

/- The idea of `open_locale cyclotomic` is that it provides some of these instances when needed,
but sadly its implementation is so unsafe that using it here creates a lot of diamonds.
We instead put some safe specialised instances here, and we can maybe look at generalising them
later, when this is needed. Most results from here on genuinely only work for ℚ, so this is
very fine for the moment. -/

instance safe {p : ℕ+} := is_cyclotomic_extension.number_field {p} ℚ $ cyclotomic_field p ℚ
instance safe' {p : ℕ+} := is_cyclotomic_extension.finite_dimensional {p} ℚ $ cyclotomic_field p ℚ

instance cyclotomic_field.class_group_finite {p : ℕ+} :
  fintype (class_group $ 𝓞 (cyclotomic_field p ℚ)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field p ℚ)
  absolute_value.abs_is_admissible

end safe_instances

variables (n p : ℕ) [fact p.prime]

instance {p : ℕ} [hp : fact p.prime] : fact (0 < p) := ⟨hp.out.pos⟩

-- note that this definition can be annoying to work with whilst #14984 isn't merged.
/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group -/
def is_regular_number [hn : fact (0 < n)]  : Prop :=
n.coprime $ fintype.card $ class_group (𝓞 $ cyclotomic_field ⟨n, hn.out⟩ ℚ)

/-- The definition of regular primes. -/
def is_regular_prime : Prop := is_regular_number p

/-- A prime number is Bernoulli regular if it does not divide the numerator of any of
the first `p - 3` (non-zero) Bernoulli numbers-/
def is_Bernoulli_regular : Prop :=
∀ i ∈ finset.range((p - 3) / 2), ((bernoulli 2 * i).num : zmod p) ≠ 0

/--A prime is super regular if its regular and Bernoulli regular.-/
def is_super_regular : Prop :=
 is_regular_number p ∧ is_Bernoulli_regular p

section two_regular

variables (A K : Type*) [comm_ring A] [is_domain A] [field K] [algebra A K] [is_fraction_ring A K]

variables (L : Type*) [field L] [algebra K L]

/-- The second cyclotomic field is equivalent to the base field. -/
def cyclotomic_field_two_equiv [is_cyclotomic_extension {2} K L] : L ≃ₐ[K] K :=
begin
  suffices : is_splitting_field K K (cyclotomic 2 K),
  { letI : is_splitting_field K L (cyclotomic 2 K) :=
      is_cyclotomic_extension.splitting_field_cyclotomic 2 K L,
    exact (is_splitting_field.alg_equiv L (cyclotomic 2 K)).trans
      (is_splitting_field.alg_equiv K $ cyclotomic 2 K).symm },
  exact ⟨by simpa using @splits_X_sub_C _ _ _ _ (ring_hom.id K) (-1), by simp⟩,
end

.

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def ring_equiv.to_int_alg_equiv {R S} [ring R] [ring S] [algebra ℤ R] [algebra ℤ S] (f : R ≃+* S) :
  R ≃ₐ[ℤ] S :=
{ commutes' := λ n, show (f : R →+* S) _ = _, by simp,
  .. f }
--todo : `fun_like` on the `int/cast` file.

instance (L : Type*) [field L] [char_zero L] [is_cyclotomic_extension {2} ℚ L] :
  is_principal_ideal_ring (𝓞 L) :=
begin
  sorry
  /-
  let ζ := is_cyclotomic_extension.zeta 2 ℚ (cyclotomic_field 2 ℚ),
  let hζ := is_cyclotomic_extension.zeta_spec 2 ℚ (cyclotomic_field 2 ℚ),
  have : fact (nat.prime (2 : ℕ+)) := ⟨prime_two⟩,
  haveI := cyclotomic_field.is_cyclotomic_extension 2 ℚ,
  haveI := is_cyclotomic_extension.rat.is_integral_closure_adjoing_singleton_of_prime hζ,
  let f := ((cyclotomic_field_two_equiv ℚ : cyclotomic_field 2 ℚ ≃+* ℚ).to_int_alg_equiv).subalgebra_map (algebra.adjoin ℤ {ζ}),
  suffices : algebra.adjoin ℤ {ζ} = ⊥,
  { let := is_integral_closure.equiv ℤ (𝓞 (cyclotomic_field 2 ℚ)) (cyclotomic_field 2 ℚ) (algebra.adjoin ℤ ({ζ} : set (cyclotomic_field 2 ℚ))), }, -/
end

example : is_regular_number 2 :=
begin
  rw is_regular_number,
  convert coprime_one_right _,
  dsimp,
  rw card_class_group_eq_one_iff,
  sorry
end

end two_regular
