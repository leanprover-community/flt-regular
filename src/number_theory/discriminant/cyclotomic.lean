import ring_theory.adjoin.power_basis

import number_theory.discriminant.basic
import number_theory.cyclotomic.cyclotomic_units

universes u v

open is_cyclotomic_extension algebra

variables (K : Type u) [field K] [char_zero K] (p : ℕ+) [is_cyclotomic_extension {p} ℚ K]

local notation `pb` := zeta'.power_basis p ℚ K
local notation `ζ` := zeta' p ℚ K

lemma norm_zeta'_sub_one : norm ℚ (ζ - 1) = p :=
begin
  sorry
end
