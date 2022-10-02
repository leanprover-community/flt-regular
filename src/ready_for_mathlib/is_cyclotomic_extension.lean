import number_theory.cyclotomic.basic

variables {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]
variables (S : set ℕ+)

namespace is_cyclotomic_extension

open algebra

lemma equiv [h : is_cyclotomic_extension S R A] (f : A ≃ₐ[R] B) : is_cyclotomic_extension S R B :=
begin
  refine (iff_adjoin_eq_top _ _ _).2 ⟨λ s hs, _, _⟩,
  { obtain ⟨a, ha⟩ := ((is_cyclotomic_extension_iff S R A).1 h).1 hs,
    exact ⟨f a, ha.map_of_injective f.injective⟩ },
  { have : (f.symm) '' {b : B | ∃ (s : ℕ+), s ∈ S ∧ b ^ (s : ℕ) = 1} =
      {a : A | ∃ (s : ℕ+), s ∈ S ∧ a ^ (s : ℕ) = 1},
    { refine set.ext (λ x, ⟨λ hx, _, λ hx, _⟩),
      { simp only [set.mem_image, set.mem_set_of_eq] at ⊢ hx,
        obtain ⟨b, ⟨n, ⟨hn, hbn⟩⟩, hxb⟩ := hx,
        refine ⟨n, ⟨hn, _⟩⟩,
        rw [← hxb, ← alg_equiv.map_pow, hbn, alg_equiv.map_one] },
      { simp only [set.mem_image, set.mem_set_of_eq] at ⊢ hx,
        obtain ⟨n, ⟨hn, hxn⟩⟩ := hx,
        refine ⟨f x, ⟨⟨n, ⟨hn, _⟩⟩, by simp⟩⟩,
        { rw [← alg_equiv.map_pow, hxn, alg_equiv.map_one] } } },
    refine _root_.eq_top_iff.2 (λ x hx, _),
    suffices : f.symm x ∈
      (adjoin R {b : B | ∃ (s : ℕ+), s ∈ S ∧ b ^ ↑s = 1}).map f.symm.to_alg_hom,
    { obtain ⟨b, hb, Hb⟩ := subalgebra.mem_map.1 this,
      simp only [alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom,
        embedding_like.apply_eq_iff_eq] at Hb,
      rwa [← Hb] },
    rw [← adjoin_image, alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, this,
      ((iff_adjoin_eq_top _ _ _).1 h).2],
    exact mem_top }
end

end is_cyclotomic_extension
