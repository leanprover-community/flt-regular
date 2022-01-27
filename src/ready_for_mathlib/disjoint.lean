import data.finset.basic

namespace finset

lemma range_disjoint_add_left_embedding (a b : ℕ) :
  disjoint (range a) (map (add_left_embedding a) (range b)) :=
begin
  intros k hk,
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, add_left_embedding_apply,
    mem_inter] at hk,
  obtain ⟨a, haQ, ha⟩ := hk.2,
  simpa [← ha] using hk.1,
end

lemma range_disjoint_add_right_embedding (a b : ℕ) :
  disjoint (range a) (map (add_right_embedding a) (range b)) :=
begin
  intros k hk,
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, add_left_embedding_apply,
    mem_inter] at hk,
  obtain ⟨a, haQ, ha⟩ := hk.2,
  simpa [← ha] using hk.1,
end

end finset
