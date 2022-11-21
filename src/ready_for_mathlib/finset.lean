import data.finset.basic

namespace finset

@[simp]
lemma range_filter_eq {n m : ℕ} : (range n).filter (= m) = if m < n then {m} else ∅ :=
begin
  convert filter_eq (range n) m,
  { ext, exact comm },
  { simp }
end

end finset
