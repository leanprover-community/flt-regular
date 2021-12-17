import number_theory.class_number.finite
import field_theory.splitting_field

import number_theory.cyclotomic.class_group
import ready_for_mathlib.cyclotomic.basic

/-!
# Regular primes

## Main definitions

* `is_regular_number`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/


noncomputable theory
open nat polynomial

open number_field

variables (n : ℕ) [fact (0 < n)]
-- local attribute [priority 5, instance] rat.normed_field -- hack to avoid diamond?

open_locale classical
-- set_option trace.type_context.is_def_eq true
-- set_option trace.class_instances true
-- set_option pp.all true

/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group -/
def is_regular_number : Prop :=
n.coprime (fintype.card (class_group (cyclotomic_ring ⟨n, fact.out _⟩ ℤ ℚ)
                                     (cyclotomic_field ⟨n, fact.out _⟩ ℚ)))

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
