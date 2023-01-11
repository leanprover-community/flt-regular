/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import number_theory.cyclotomic.primitive_roots
import ring_theory.polynomial.cyclotomic.eval

noncomputable theory

open_locale big_operators non_zero_divisors number_field
open number_field polynomial finset module units submodule

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

namespace is_primitive_root

variable {B}

variable (B)

end is_primitive_root

namespace is_cyclotomic_extension

variables [is_cyclotomic_extension {n} A B]

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

open is_cyclotomic_extension

open is_cyclotomic_extension

section cyclotomic_unit

variable {n}

namespace cyclotomic_unit

-- I don't want to bother Leo, but I wonder if this can be automated in Lean4
-- (if they were 0 < n → 1 < n, it would work already!)
lemma _root_.nat.one_lt_of_ne : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → 1 < n
| 0 h _ := absurd rfl h
| 1 _ h := absurd rfl h
| (n+2) _ _ := n.one_lt_succ_succ

-- this result holds for all primitive roots; dah.
lemma associated_one_sub_pow_primitive_root_of_coprime {n j k : ℕ} {ζ : A}
  (hζ : is_primitive_root ζ n) (hk : k.coprime n) (hj : j.coprime n) :
  associated (1 - ζ ^ j) (1 - ζ ^ k) :=
begin
  suffices : ∀ {j : ℕ}, j.coprime n → associated (1 - ζ) (1 - ζ ^ j),
  { exact (this hj).symm.trans (this hk) },
  clear' k j hk hj,
  refine λ j hj, associated_of_dvd_dvd ⟨∑ i in range j, ζ ^ i,
    by rw [← geom_sum_mul_neg, mul_comm]⟩ _,
  -- is there an easier way to do this?
  rcases eq_or_ne n 0 with rfl | hn',
  { simp [j.coprime_zero_right.mp hj] },
  rcases eq_or_ne n 1 with rfl | hn,
  { simp [is_primitive_root.one_right_iff.mp hζ] },
  replace hn := n.one_lt_of_ne hn' hn,
  obtain ⟨m, hm⟩ := nat.exists_mul_mod_eq_one_of_coprime hj hn,
  use (∑ i in range m, (ζ ^ j) ^ i),
  have : ζ = (ζ ^ j) ^ m,
  { rw [←pow_mul, pow_eq_mod_order_of, ←hζ.eq_order_of, hm, pow_one] },
  nth_rewrite 0 this,
  rw [← geom_sum_mul_neg, mul_comm]
end

lemma is_primitive_root.sum_pow_unit {n k : ℕ} {ζ : A} (hn : 2 ≤ n) (hk : k.coprime n)
(hζ : is_primitive_root ζ n) : is_unit (∑ (i : ℕ) in range k, ζ^(i : ℕ)) :=
begin
  have h1 : (1 : ℕ).coprime n, by {exact nat.coprime_one_left n, },
  have := associated_one_sub_pow_primitive_root_of_coprime _ hζ hk h1,
  simp at this,
  rw associated at this,
  have h2 := mul_neg_geom_sum ζ k,
  obtain ⟨u, hu⟩ := this,
  have := u.is_unit,
  convert this,
  rw ←hu at h2,
  simp at h2,
  cases h2,
  exact h2,
  exfalso,
  have hn1 : 1 < n, by {linarith},
  have  hp := is_primitive_root.pow_ne_one_of_pos_of_lt hζ one_pos hn1,
  simp at *,
  rw sub_eq_zero at h2,
  rw ←h2 at hp,
  simp only [eq_self_iff_true, not_true] at hp,
  exact hp,
end

lemma is_primitive_root.zeta_pow_sub_eq_unit_zeta_sub_one {p i j : ℕ} {ζ : A} (hn : 2 ≤ p) (hp : p.prime )
  (hi : i < p) (hj : j < p) (hij : i ≠ j) (hζ : is_primitive_root ζ p) :
  ∃ (u : Aˣ), (ζ^i - ζ^j ) = u * (1- ζ) :=
begin
  by_cases hilj : j < i,
  have h1 : (ζ^i - ζ^j) = ζ^j * (ζ^(i-j)-1), by {ring_exp, rw pow_mul_pow_sub _ hilj.le,
    rw add_comm,},
  rw h1,
  have h2 := mul_neg_geom_sum ζ (i-j),
  have hic : (i-j).coprime p, by {rw nat.coprime_comm, apply nat.coprime_of_lt_prime _ _ hp,
    apply nat.sub_pos_of_lt hilj,
    by_cases hj : 0 < j,
    apply lt_trans _ hi,
    apply nat.sub_lt_of_pos_le _ _ hj hilj.le,
    simp only [not_lt, _root_.le_zero_iff] at hj,
    rw hj,
    simp only [tsub_zero],
    exact hi,},
  have h3 : is_unit (-(ζ^(j))*(∑ (k : ℕ) in range (i-j), ζ^(k : ℕ))),
    by {apply is_unit.mul _ (is_primitive_root.sum_pow_unit _ hn hic hζ), apply is_unit.neg,
      apply is_unit.pow, apply hζ.is_unit hp.pos,  },
  obtain ⟨v, hv⟩ := h3,
  use v,
  rw hv,
  rw mul_comm at h2,
  rw mul_assoc,
  rw h2,
  ring,
  simp at *,
  have h1 : (ζ^i - ζ^j) = ζ^i * (1-ζ^(j-i)), by {ring_exp, simp, rw pow_mul_pow_sub _ hilj,},
  rw h1,
  have h2 := mul_neg_geom_sum ζ (j-i),
  have hjc : (j-i).coprime p, by {rw nat.coprime_comm,
    apply nat.coprime_of_lt_prime _ _ hp,
    have hilj' : i < j, by {rw lt_iff_le_and_ne, simp [hij, hilj], },
    apply nat.sub_pos_of_lt hilj',
    by_cases hii : 0 < i,
    apply lt_trans _ hj,
    apply nat.sub_lt_of_pos_le _ _ hii hilj,
    simp only [not_lt, _root_.le_zero_iff] at hii,
    rw hii,
    simp only [tsub_zero],
    exact hj,
  },
  have h3 : is_unit ((ζ^(i))*(∑ (k : ℕ) in range (j-i), ζ^(k : ℕ))), by {
    apply is_unit.mul _ (is_primitive_root.sum_pow_unit _ hn hjc hζ), apply is_unit.pow,
    apply hζ.is_unit hp.pos,},
   obtain ⟨v, hv⟩ := h3,
  use v,
  rw hv,
  rw mul_comm at h2,
  rw mul_assoc,
  rw h2,


end

/-
def unitlem2 {n k : ℕ} {ζ : A} (hk : nat.coprime n k)
(hζ : is_primitive_root ζ n) : Aˣ :=
{ val := (∑ (i : finset.range k), ζ^(i : ℕ)),
  inv := (ζ-1)  ,
  val_inv := admit,
  inv_val := admit,

}




variable (n)

instance : is_localization ((ring_of_integers (cyclotomic_field n K)))⁰ (cyclotomic_field n K) :=
admit

lemma prime_ideal_eq_pow_cyclotomic [hn : fact ((n : ℕ).prime)] :
  (span_singleton _ n : fractional_ideal RR⁰ L) =
  (span_singleton _ (1 - (zeta_runity n K L)) ^ ((n : ℕ) - 1) : fractional_ideal RR⁰ L) :=
  --(mk0 (p : cyclotomic_field p) (by norm_num [hn.ne_zero]))
begin
  rw fractional_ideal.span_singleton_pow,
  apply coe_to_submodule_injective,
  simp only [coe_span_singleton, coe_coe],
  -- rw ideal.span_singleton_eq_span_singleton,
  simp only [submodule.span_singleton_eq_span_singleton],
  rw ← eval_one_cyclotomic_prime,
  --rw calc
  --  eval 1 (cyclotomic n (cyclotomic_field n)) = _ : by simp_rw
  --    cyclotomic_eq_prod_X_sub_primitive_roots (zeta_primitive_root n _)
  --                      ... = _ : by simp only [polynomial.eval_sub, polynomial.eval_C,
  --                                  polynomial.eval_prod, polynomial.eval_X],

  -- apply span_singleton_eq_span_singleton_,
  admit,
end -/

end cyclotomic_unit

end cyclotomic_unit

end is_cyclotomic_extension
