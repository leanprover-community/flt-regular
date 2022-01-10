import field_theory.intermediate_field

namespace intermediate_field

open_locale big_operators

variables {K L ι : Type*} [field K] [field L] [algebra K L] {S : intermediate_field K L}

lemma coe_sum [fintype ι] (f : ι → S) : (↑∑ i, f i : L) = ∑ i, (f i : L) :=
begin
  classical,
  induction finset.univ using finset.induction_on with i s hi H,
  { simp },
  { rw [finset.sum_insert hi, coe_add, H, finset.sum_insert hi] }
end

lemma coe_prod [fintype ι] (f : ι → S) : (↑∏ i, f i : L) = ∏ i, (f i : L) :=
begin
  classical,
  induction finset.univ using finset.induction_on with i s hi H,
  { simp },
  { rw [finset.prod_insert hi, coe_mul, H, finset.prod_insert hi] }
end

end intermediate_field
