import ring_theory.adjoin.basic

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A] {s : set A}

namespace algebra

-- lemma adjoin_induction' {p : adjoin R s → Prop} (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_adjoin h⟩)
--   (Halg : ∀ (r : R), p ⟨(algebra_map R _) r, subalgebra.algebra_map_mem _ r⟩)
--   (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) (x : adjoin R s) :
--   p x :=
-- subtype.rec_on x $ λ x hx, begin
--   refine exists.elim _ (λ (hx : x ∈ adjoin R s) (hc : p ⟨x, hx⟩), hc),
--   refine adjoin_induction hx (λ x hx, ⟨subset_adjoin hx, Hs x hx⟩)
--     (λ r, ⟨subalgebra.algebra_map_mem _ r, Halg r⟩)
--     (λ x y hx hy, exists.elim hx $ λ hx' hx, exists.elim hy $ λ hy' hy,
--     ⟨subalgebra.add_mem _ hx' hy', Hadd _ _ hx hy⟩) (λ x y hx hy, exists.elim hx $ λ hx' hx,
--     exists.elim hy $ λ hy' hy, ⟨subalgebra.mul_mem _ hx' hy', Hmul _ _ hx hy⟩),
-- end

lemma adjoin_idem (s: set A) {x : adjoin R s} :
  x ∈ adjoin R {a : adjoin R s | (a : A) ∈ s} ↔ (x : A) ∈ adjoin R s :=
begin
  refine ⟨λ hx, adjoin_induction hx (λ x h, x.2)
                  (subalgebra.algebra_map_mem _)
                  (λ x y, subalgebra.add_mem _)
                  (λ x y, subalgebra.mul_mem _),
          λ hx, adjoin_induction' (λ a ha, _) (λ r, _) (λ x y hx hy, _) (λ x y hx hy, _) x⟩,
  { exact subset_adjoin ha },
  { exact subalgebra.algebra_map_mem _ r },
  { exact subalgebra.add_mem _ hx hy },
  { exact subalgebra.mul_mem _ hx hy }
end

end algebra
