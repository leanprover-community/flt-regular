
import number_theory.class_number.finite
import field_theory.splitting_field
import number_theory.cyclotomic.class_group
import number_theory.bernoulli

/-!
# Regular primes

## Main definitions

* `is_regular_number`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/


noncomputable theory
open nat polynomial

open number_field

variables (n p : ℕ) [fact (0 < n)] [fact p.prime]
-- local attribute [priority 5, instance] rat.normed_field -- hack to avoid diamond?

open_locale classical
-- set_option trace.type_context.is_def_eq true
-- set_option trace.class_instances true
-- set_option pp.all true

-- can we just make this a pnat definition please lord
/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group -/
def is_regular_number : Prop :=
n.coprime (fintype.card (class_group (cyclotomic_ring ⟨n, fact.out _⟩ ℤ ℚ)
                                     (cyclotomic_field ⟨n, fact.out _⟩ ℚ)))
/-- A prime number is Bernoulli regular if it does not divide the numerator of any of
the first `p-3` (non-zero) Bernoulli numbers-/
def is_Bernoulli_regular : Prop :=
∀ i ∈ finset.range((p-3)/2), ((bernoulli 2*i).num : zmod p) ≠ 0

/--A prime is super regular if its regular and Bernoulli regular.-/
def is_super_regular : Prop :=
 is_regular_number p ∧ is_Bernoulli_regular p

section two_regular

variables (A K : Type*) [comm_ring A] [is_domain A] [field K] [algebra A K] [is_fraction_ring A K]

local attribute [instance] cyclotomic_ring.algebra_base cyclotomic_field.algebra_base

/-- The second cyclotomic field is equivalent to the base field. -/
def cyclotomic_field_two_equiv_bot : cyclotomic_field 2 K ≃ₐ[K] K :=
begin
  suffices : is_splitting_field K K (cyclotomic 2 K),
  { exactI (is_splitting_field.alg_equiv K $ cyclotomic 2 K).symm },
  exact ⟨by simpa using @splits_X_sub_C _ _ _ _ (ring_hom.id K) (-1), by simp⟩,
end

/-- The second cyclotomic ring is equivalent to the base ring. -/
def cyclotomic_ring_two_equiv_bot : cyclotomic_ring 2 A K ≃ₐ[A] A :=
begin
  refine alg_equiv.trans _ (algebra.bot_equiv_of_injective $ no_zero_smul_divisors.algebra_map_injective A $ cyclotomic_field 2 K),
  apply subalgebra.equiv_of_eq,
  rw [eq_bot_iff, algebra.adjoin_le_iff],
  intro x,
  simp only [pnat.coe_bit0, pnat.one_coe, sq_eq_one_iff, set_like.mem_coe],
  rintro (rfl | rfl),
  { exact subalgebra.one_mem _ },
  { exact subalgebra.neg_mem _ (subalgebra.one_mem _) }
end

example : is_regular_number 2 :=
begin
  rw is_regular_number,
  convert coprime_one_right _,
  suffices : is_principal_ideal_ring (cyclotomic_ring 2 ℤ ℚ), --TC does't wanna play ball
  { convert card_class_group_eq_one_iff.mpr _,
    apply_instance,
    exact @@is_principal_ideal_ring.is_dedekind_domain _ _ _ this,
    exact this },
  let f := (cyclotomic_ring_two_equiv_bot ℤ ℚ).symm.to_ring_equiv,
  exact is_principal_ideal_ring.of_surjective f.to_ring_hom f.surjective
end

end two_regular
