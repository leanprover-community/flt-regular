import ring_theory.polynomial.cyclotomic.basic
import ready_for_mathlib.ne_zero

open polynomial nat
open_locale big_operators

section no_pr_yet

-- I'll wait for `ne_zero` before merging these
lemma roots_cyclotomic_nodup {n : ℕ} {R : Type*} [comm_ring R] [is_domain R] [h : ne_zero (n : R)] :
  (cyclotomic n R).roots.nodup :=
begin
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem,
  { exact h.symm ▸ multiset.nodup_zero },
  rw [mem_roots $ cyclotomic_ne_zero n R, is_root_cyclotomic_iff] at hζ,
  refine multiset.nodup_of_le (roots.le_of_dvd (X_pow_sub_C_ne_zero (pos_of_ne_zero_coe n R) 1) $
                               cyclotomic.dvd_X_pow_sub_one n R) hζ.nth_roots_nodup,
end

lemma primitive_roots_eq_roots_cyclotomic {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  [h : ne_zero (n : R)] : primitive_roots n R = ⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ :=
by { ext, simp [cyclotomic_ne_zero n R, is_root_cyclotomic_iff,
                mem_primitive_roots, pos_of_ne_zero_coe n R] }

end no_pr_yet
