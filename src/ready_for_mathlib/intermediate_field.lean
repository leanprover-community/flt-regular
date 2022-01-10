import field_theory.intermediate_field

namespace intermediate_field

open_locale big_operators

variables {K L ι : Type*} [field K] [field L] [algebra K L] {S : intermediate_field K L}

lemma coe_sum [fintype ι] (f : ι → S) : (∑ i, f i : L) = ∑ i, (f i : L) := rfl

end intermediate_field
