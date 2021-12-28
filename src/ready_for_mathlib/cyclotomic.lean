import ring_theory.polynomial.cyclotomic.basic

open polynomial nat
open_locale big_operators

section pr_11063
namespace polynomial

lemma cyclotomic_prime_mul_X_sub_one (R : Type*) [comm_ring R] (p : ℕ) [hn : fact (nat.prime p)] :
  (cyclotomic p R) * (X - 1) = X ^ p - 1 :=
begin
  rw cyclotomic_eq_geom_sum hn.out,
  exact geom_sum_mul X p,
end

end polynomial
end pr_11063

section no_pr_yet

-- this requires two of the above; i will wait for one of them to merge to master before;
-- I don't want to have a complicated PR structure for two lemmas
lemma roots_cyclotomic_nodup {n : ℕ} {R : Type*} [comm_ring R] [is_domain R] (hn : (n : R) ≠ 0) :
  (cyclotomic n R).roots.nodup :=
begin
  have hn' : 0 < n := (show n ≠ 0, by { rintro rfl, contradiction }).bot_lt,
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem,
  { exact h.symm ▸ multiset.nodup_zero },
  rw [mem_roots $ cyclotomic_ne_zero n R, is_root_cyclotomic_iff hn] at hζ,
  refine multiset.nodup_of_le (roots.le_of_dvd (X_pow_sub_C_ne_zero hn' 1) $
                               cyclotomic.dvd_X_pow_sub_one n R) _,
  exact hζ.nth_roots_nodup
end

lemma primitive_roots_eq_roots_cyclotomic {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  (hn : (n : R) ≠ 0) : primitive_roots n R = ⟨(cyclotomic n R).roots, roots_cyclotomic_nodup hn⟩ :=
let hn' : 0 < n := (show n ≠ 0, by { rintro rfl, contradiction }).bot_lt in
by { ext, simp [cyclotomic_ne_zero n R, is_root_cyclotomic_iff hn, mem_primitive_roots hn'] }

end no_pr_yet
