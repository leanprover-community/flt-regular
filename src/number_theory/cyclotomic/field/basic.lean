import number_theory.class_number.finite
import number_theory.class_number.admissible_abs
import ring_theory.polynomial.cyclotomic
import field_theory.splitting_field
import number_theory.number_field
import algebra.char_p.algebra

variables (n : ℕ) [hn : fact (0 < n)] (F K : Type*) [field F] [field K] [algebra F K]

open_locale classical

open polynomial

section cyclotomic_polynomial

include hn
instance polynomial.cyclotomic_rat.irreducible :
  irreducible (cyclotomic n ℚ) :=
by { simpa using ((is_primitive.int.irreducible_iff_irreducible_map_cast
    (monic.is_primitive (cyclotomic.monic n ℤ))).1 (cyclotomic.irreducible hn.out)) }

end cyclotomic_polynomial

section is_cyclotomic_field

abbreviation is_cyclotomic_field := is_splitting_field F K (X ^ n - 1)

namespace is_cyclotomic_field

instance splitting_field [char_zero K] [h : is_cyclotomic_field n ℚ K] :
is_splitting_field ℚ K (X ^ n - 1) := h

instance finite_dimensional [char_zero K] [is_cyclotomic_field n ℚ K] :
  finite_dimensional ℚ K :=
is_splitting_field.finite_dimensional _ (X ^ n - 1)

instance number_field [char_zero K] [is_cyclotomic_field n ℚ K] :
  number_field K :=
{ to_char_zero := infer_instance,
  to_finite_dimensional := infer_instance }

instance [char_zero K] [is_cyclotomic_field n ℚ K] : is_splitting_field ℚ K (cyclotomic n ℚ) :=
sorry

open finite_dimensional
lemma degree [char_zero K] [is_cyclotomic_field n ℚ K] : finrank ℚ K = nat.totient n :=
begin
  have : (cyclotomic n ℚ) ≠ 0 := cyclotomic_ne_zero n ℚ,
  have := (adjoin_root.power_basis this).finrank, -- another diamond if I try to combine these lines
  simp [nat_degree_cyclotomic] at this,
  convert this, -- ew rat algebra diamond
  haveI : subsingleton (algebra ℚ (adjoin_root (cyclotomic n ℚ))) := rat.algebra_rat_subsingleton,
  sorry
  --exact subsingleton.elim _ _,
end

end is_cyclotomic_field

end is_cyclotomic_field

section cyclotomic_field

@[derive [field]]
def cyclotomic_field [fact (0 < n)] : Type* := adjoin_root (cyclotomic n ℚ)

namespace cyclotomic_field
variable {n}

include hn
instance : char_zero (cyclotomic_field n) :=
begin
  haveI : char_zero ℚ := sorry,
  exact char_zero_of_injective_algebra_map (algebra_map ℚ (adjoin_root (cyclotomic n ℚ))).injective,
end

instance : is_cyclotomic_field n ℚ (cyclotomic_field n) :=
begin
  sorry
  -- delta cyclotomic_field, convert is_splitting_field.splitting_field (@cyclotomic n ℚ _),
  -- haveI : subsingleton (algebra ℚ (cyclotomic n ℚ).splitting_field) := rat.algebra_rat_subsingleton,
  -- apply subsingleton.elim,
end

end cyclotomic_field

end cyclotomic_field

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
