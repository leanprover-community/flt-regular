import number_theory.cyclotomic.primitive_roots

universes u v

namespace is_primitive_root

variables {K : Type u} [field K] {L : Type v} [field L] [algebra K L] {ζ : L}

open polynomial algebra is_cyclotomic_extension set

local attribute [instance] is_cyclotomic_extension.finite_dimensional
local attribute [instance] is_cyclotomic_extension.is_galois

lemma pow_prime_ne_two_pow_sub_one_norm {p : ℕ+} [ne_zero ((p : ℕ) : K)] {k : ℕ}
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) [hpri : fact (p : ℕ).prime]
  [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))  {s : ℕ}
  (hirr₁ : irreducible (cyclotomic (↑(p ^ (k - s + 1)) : ℕ) K)) (h : p ≠ 2) (hs : s ≤ k) :
  norm K (ζ ^ ((p : ℕ) ^ s) - 1) = p ^ ((p : ℕ) ^ s) :=
begin
  haveI : ne_zero ((↑(p ^ (k + 1)) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pnat.pow_coe] at hzero,
    simpa [ne_zero.ne ((p : ℕ) : K)] using hzero },
  haveI : ne_zero ((↑(p ^ (k - s + 1)) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pnat.pow_coe] at hzero,
    simpa [ne_zero.ne ((p : ℕ) : K)] using hzero },

  let η := ζ ^ ((p : ℕ) ^ s) - 1,
  let η₁ : K⟮η⟯ := intermediate_field.adjoin_simple.gen K η,
  have hη : is_primitive_root (η + 1) (p ^ (k + 1 - s)),
  { rw [sub_add_cancel],
    refine is_primitive_root.pow (p ^ (k + 1)).pos hζ _,
    rw [pnat.pow_coe, ← pow_add, add_comm s, nat.sub_add_cancel (le_trans hs (nat.le_succ k))] },
  haveI : is_cyclotomic_extension {p ^ (k - s + 1)} K K⟮η⟯,
  { suffices : is_cyclotomic_extension {p ^ (k - s + 1)} K K⟮η + 1⟯.to_subalgebra,
    { have H : K⟮η + 1⟯.to_subalgebra = K⟮η⟯.to_subalgebra,
      { simp only [intermediate_field.adjoin_simple_to_subalgebra_of_integral _ _
          (is_cyclotomic_extension.integral {p ^ (k + 1)} K L _)],
        refine subalgebra.ext (λ x, ⟨λ hx, adjoin_le _ hx, λ hx, adjoin_le _ hx⟩),
        { simp only [singleton_subset_iff, set_like.mem_coe],
          exact subalgebra.add_mem _ (subset_adjoin (mem_singleton η)) (subalgebra.one_mem _) },
        { simp only [singleton_subset_iff, set_like.mem_coe],
          nth_rewrite 0 [← add_sub_cancel η 1],
          refine subalgebra.sub_mem _ (subset_adjoin (mem_singleton _)) (subalgebra.one_mem _) } },
      rw [H] at this,
      exact this },
    rw [intermediate_field.adjoin_simple_to_subalgebra_of_integral _ _
      (is_cyclotomic_extension.integral {p ^ (k + 1)} K L _)],
    have hη' : is_primitive_root (η + 1) ↑(p ^ (k + 1 - s)) := by simpa using hη,
    convert hη'.adjoin_is_cyclotomic_extension K,
    rw [nat.sub_add_comm hs] },
  replace hη : is_primitive_root (η₁ + 1) ↑(p ^ (k - s + 1)),
  { refine ⟨_, λ l hl, _⟩,
    { rw [← subalgebra.coe_eq_one, subalgebra.coe_pow, pnat.pow_coe],
      convert hη.1,
      rw [nat.sub_add_comm hs] },
    { rw [← subalgebra.coe_eq_one, subalgebra.coe_pow] at hl,
      rw [pnat.pow_coe],
      convert hη.2 _ hl,
      rw [nat.sub_add_comm hs] } },
  rw [norm_eq_norm_adjoin K],
  { have : p ^ (k - s + 1) ≠ 2, sorry,
    have H := hη.sub_one_norm_is_prime_pow _ hirr₁ this,
    swap, { rw [pnat.pow_coe], exact hpri.1.is_prime_pow.pow (nat.succ_ne_zero _) },
    rw [add_sub_cancel] at H,
    rw [H, coe_coe],
    congr,
    { rw [pnat.pow_coe, nat.pow_min_fac, hpri.1.min_fac_eq], exact nat.succ_ne_zero _ },
    have := finite_dimensional.finrank_mul_finrank K K⟮η⟯ L,
    rw [is_cyclotomic_extension.finrank L hirr, is_cyclotomic_extension.finrank K⟮η⟯ hirr₁,
      pnat.pow_coe, pnat.pow_coe, nat.totient_prime_pow hpri.out (k - s).succ_pos,
      nat.totient_prime_pow hpri.out k.succ_pos, mul_comm _ (↑p - 1), mul_assoc,
      mul_comm (↑p ^ (k.succ - 1))] at this,
    replace this := nat.eq_of_mul_eq_mul_left (tsub_pos_iff_lt.2 (nat.prime.one_lt hpri.out)) this,
    have Hex : k.succ - 1 = (k - s).succ - 1 + s,
    { simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
      exact (nat.sub_add_cancel hs).symm },
    rw [Hex, pow_add] at this,
    exact nat.eq_of_mul_eq_mul_left (pow_pos hpri.out.pos _) this },
  all_goals { apply_instance }
end

end is_primitive_root
