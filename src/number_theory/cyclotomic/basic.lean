import number_theory.class_number.finite
import number_theory.class_number.admissible_abs
import ring_theory.polynomial.cyclotomic
import field_theory.splitting_field
import number_theory.number_field
import algebra.char_p.algebra

open polynomial
variable (n : ℕ)
open_locale classical
instance aaaaaaaa [hn : fact (0 < n)] : irreducible (cyclotomic n ℚ) :=
by { simpa using ((is_primitive.int.irreducible_iff_irreducible_map_cast
    (monic.is_primitive (cyclotomic.monic n ℤ))).1 (cyclotomic.irreducible hn.out)) }

@[derive [field]]
def cyclotomic_field [fact (0 < n)] : Type* := adjoin_root (cyclotomic n ℚ)

variable [fact (0 < n)]
instance : char_zero (cyclotomic_field n) :=
begin
  apply char_p.char_p_to_char_zero _,
  haveI : algebra ℚ (cyclotomic_field n),
  { delta cyclotomic_field, apply_instance, },
  rw ← algebra.char_p_iff ℚ,
  exact char_p.of_char_zero ℚ,
end

instance : is_splitting_field ℚ (cyclotomic_field n) (cyclotomic n ℚ) :=
begin
  sorry
  -- delta cyclotomic_field, convert is_splitting_field.splitting_field (@cyclotomic n ℚ _),
  -- haveI : subsingleton (algebra ℚ (cyclotomic n ℚ).splitting_field) := rat.algebra_rat_subsingleton,
  -- apply subsingleton.elim,
end

instance : finite_dimensional ℚ (cyclotomic_field n) :=
begin
  delta cyclotomic_field,
  exact polynomial.is_splitting_field.finite_dimensional (cyclotomic_field n) (@cyclotomic n ℚ _),
end

namespace cyclotomic_field
variable {n}

instance : number_field (cyclotomic_field n) := number_field.mk
-- TODO why does apply instance niet doen

open finite_dimensional
lemma degree : finrank ℚ (cyclotomic_field n) = nat.totient n :=
begin
  delta cyclotomic_field,
  have : (cyclotomic n ℚ) ≠ 0 := cyclotomic_ne_zero n ℚ,
  -- have := adjoin_root.power_basis (monic.ne_zero this),
  have := (adjoin_root.power_basis this).finrank, -- another diamond if I try to combine these lines
  simp [nat_degree_cyclotomic] at this,
  convert this, -- ew rat algebra diamond
  haveI : subsingleton (algebra ℚ (adjoin_root (cyclotomic n ℚ))) := rat.algebra_rat_subsingleton,
  exact subsingleton.elim _ _,
end

end cyclotomic_field

section cyclotomic_ring

noncomputable
def cyclotomic_ring (n : ℕ) [fact (0 < n)] :=
number_field.ring_of_integers (cyclotomic_field n)

instance (n : ℕ) [fact (0 < n)] : is_fraction_ring (cyclotomic_ring n) (cyclotomic_field n) :=
number_field.ring_of_integers.is_fraction_ring

instance (n : ℕ) [fact (0 < n)] : is_integral_closure (cyclotomic_ring n) ℤ (cyclotomic_field n) :=
integral_closure.is_integral_closure ℤ (cyclotomic_field n)

end cyclotomic_ring

-- Junk here:
-- set_option pp.all true
-- local attribute [priority 0, instance] rat.field
-- local attribute [priority 0, instance] normed_field.to_field
-- local attribute [priority 0, instance] linear_ordered_field.to_field
-- #check (by apply_instance : field ℚ)
-- #check (splitting_field (cyclotomic n ℚ))
-- #check (splitting_field (@cyclotomic n ℚ _))
-- #check (splitting_field (@cyclotomic n ℚ (by apply_instance)))
-- #check (splitting_field (@cyclotomic n ℚ (@comm_ring.to_ring ℚ (@field.to_comm_ring _ rat.field))))
-- #check (splitting_field (@cyclotomic n ℚ (@normed_ring.to_ring ℚ (@normed_comm_ring.to_normed_ring ℚ
--   (@normed_field.to_normed_comm_ring ℚ rat.normed_field)))))
-- #check (splitting_field (@cyclotomic n ℚ (@comm_ring.to_ring ℚ (@field.to_comm_ring _ (@linear_ordered_field.to_field.{0} rat rat.linear_ordered_field)))))
-- lemma tt :@normed_ring.to_ring ℚ (@normed_comm_ring.to_normed_ring ℚ (@normed_field.to_normed_comm_ring ℚ rat.normed_field)) =
  -- @comm_ring.to_ring ℚ (@field.to_comm_ring _ (@linear_ordered_field.to_field.{0} rat rat.linear_ordered_field)) := rfl
-- #exit
-- noncomputable theory
-- open_locale classical


-- set_option pp.all true


-- @[priority 100]
-- noncomputable
-- instance r : normed_field ℚ :=
-- { norm := λ r, ∥(r : ℝ)∥,
--   norm_mul' := λ r₁ r₂, by simp only [norm, rat.cast_mul, abs_mul],
--   dist_eq := λ r₁ r₂, by simp only [rat.dist_eq, norm, rat.cast_sub],
--   ..rat.field }

-- set_option pp.all true
-- lemma rr :  @normed_ring.to_ring.{0} rat
--     (@normed_comm_ring.to_normed_ring.{0} rat (@normed_field.to_normed_comm_ring.{0} rat rat.normed_field))
--     =
--   @division_ring.to_ring.{0} rat (@field.to_division_ring.{0} rat _) :=rfl

-- lemma ok : r = rat.normed_field :=
-- begin
--   rw r,
--   -- cases r,
--   congr,
--   all_goals {try {refl}},
-- end
-- set_option trace.class_instances true
-- set_option pp.all true
-- local attribute [priority 5, instance] rat.normed_field -- hack to avoid diamond in this def
-- #check splitting_field (cyclotomic n ℚ)
-- instance ok {L : Type*} [field L] [algebra ℚ L] {f : polynomial ℚ} [is_splitting_field ℚ L f]
--   [char_zero ℚ] :
--   char_zero L := sorry
-- noncomputable
-- instance : char_zero (cyclotomic_field n) := by {delta cyclotomic_field, apply_instance}
-- noncomputable
-- instance {L : Type*} [field L] [algebra ℚ L] {f : polynomial ℚ} [is_splitting_field ℚ L f]
--   [char_zero ℚ] :
--   char_zero (splitting_field f) := by {apply_instance, }
-- instance {L K : Type*} [field L] [field K] [algebra K L] [char_zero K] :
--   char_zero L := by {apply_instance, }

-- instance finite_dimensional' : ∀ {n}, finite_dimensional ℚ (cyclotomic_field n) :=
-- λ n, cyclotomic_field.finite_dimensional n
-- #print prefix cyclotomic_field

-- lemma  test :
--   @finite_dimensional.{0 0} rat (cyclotomic_field n) rat.division_ring
--     (@ring.to_add_comm_group.{0} (cyclotomic_field n)
--        (@division_ring.to_ring.{0} (cyclotomic_field n)
--           (@field.to_division_ring.{0} (cyclotomic_field n) (cyclotomic_field.field n))))
--     (@algebra.to_module.{0 0} rat (cyclotomic_field n) rat.comm_semiring
--        (@ring.to_semiring.{0} (cyclotomic_field n)
--           (@division_ring.to_ring.{0} (cyclotomic_field n)
--              (@field.to_division_ring.{0} (cyclotomic_field n) (cyclotomic_field.field n))))
--        (@rat.algebra_rat.{0} (cyclotomic_field n)
--           (@field.to_division_ring.{0} (cyclotomic_field n) (cyclotomic_field.field n))
--           (@cyclotomic_field.char_zero n)))
--   = @finite_dimensional.{0 0} rat (cyclotomic_field n) rat.division_ring
--     (@ring.to_add_comm_group.{0} (cyclotomic_field n)
--        (@division_ring.to_ring.{0} (cyclotomic_field n)
--           (@field.to_division_ring.{0} (cyclotomic_field n) (cyclotomic_field.field n))))
--     (@algebra.to_module.{0 0} rat (cyclotomic_field n) rat.comm_semiring
--        (@ring.to_semiring.{0} (cyclotomic_field n)
--           (@division_ring.to_ring.{0} (cyclotomic_field n)
--              (@field.to_division_ring.{0} (cyclotomic_field n) (cyclotomic_field.field n))))
--        (cyclotomic_field.algebra n))
--        :=
--        begin
--          congr,
--          end
