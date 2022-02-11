
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

-- some nice results about class number of isom rings needed I guess
-- example : is_regular_prime 2 := -- LOOL good luck
-- begin
--   rw is_regular_prime,
--   delta cyclotomic_field,
--   delta cyclotomic,
--   simp,
--   split_ifs,
--   simpa using h,

-- end
