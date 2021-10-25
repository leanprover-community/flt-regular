import number_theory.class_number.finite
import field_theory.splitting_field
import number_theory.cyclotomic.basic
import ring_theory.polynomial.cyclotomic

/-!
# Regular primes

## Main definitions

* `foo_bar`

## Main statements

* foo_bar_unique

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][]

## Tags

-/


noncomputable theory
open nat polynomial

open number_field

variables (p : ℕ) [fact (0 < p)]
-- local attribute [priority 5, instance] rat.normed_field -- hack to avoid diamond?

open_locale classical
-- set_option trace.type_context.is_def_eq true
-- set_option trace.class_instances true
-- set_option pp.all true

-- sorrying data makes lean sad so we make it a constant instead, this should of course be provable
-- TODO this is a sorry
constant a : fintype (class_group (ring_of_integers (cyclotomic_field p)) (cyclotomic_field p))

instance todo_fintype :
  fintype (class_group (ring_of_integers (cyclotomic_field p)) (cyclotomic_field p)) := a p

def is_regular_prime : Prop :=
p.gcd (fintype.card (class_group (ring_of_integers (cyclotomic_field p)) (cyclotomic_field p))) = 1

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
