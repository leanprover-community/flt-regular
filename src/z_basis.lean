import number_theory.cyclotomic.basic

.

instance {n : ℕ+} : is_domain (adjoin_root $ polynomial.cyclotomic n ℤ) :=
begin
  suffices : prime (polynomial.cyclotomic n ℤ),
  { erw [ideal.quotient.is_domain_iff_prime, ideal.span_singleton_prime this.1],
    exact this },
  rw ←gcd_monoid.irreducible_iff_prime,
  exact polynomial.cyclotomic.irreducible n.pos,
end


noncomputable example {R S : Type*} [comm_ring R] [is_domain R] [normalized_gcd_monoid R]
  [comm_ring S] [is_domain S] [algebra R S] {x : S} (hx : is_integral R x) :
  algebra.adjoin R ({x} : set S) ≃ₐ[R] adjoin_root (minpoly R x) :=
alg_equiv.symm $ alg_equiv.of_bijective
  (alg_hom.cod_restrict
    (adjoin_root.lift_hom _ x $ minpoly.aeval R x) _
    (λ p, adjoin_root.induction_on _ p $ λ p,
      (algebra.adjoin_singleton_eq_range_aeval R x).symm ▸
        (polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩))
  ⟨(alg_hom.injective_cod_restrict _ _ _).2 $ (injective_iff_map_eq_zero _).2 $ λ p,
    adjoin_root.induction_on _ p $ λ p hp, ideal.quotient.eq_zero_iff_mem.2 $
    ideal.mem_span_singleton.2 $
    begin
      haveI : algebra (fraction_ring R) S, sorry,
      haveI : is_scalar_tower R (fraction_ring R) S, sorry,
      -- the obvious results for these two need `field S`
      apply minpoly.gcd_domain_dvd (fraction_ring R) hx,
      { -- `p` is primitive
        have := (minpoly.monic hx).is_primitive,
        -- you said this was no problem, so hopefully it isn't!
        sorry },
      { simpa using hp },
    end,
  λ y,
    let ⟨p, hp⟩ := (set_like.ext_iff.1
      (algebra.adjoin_singleton_eq_range_aeval R x) (y : S)).1 y.2 in
    ⟨adjoin_root.mk _ p, subtype.eq hp⟩⟩


instance {n} : is_cyclotomic_extension {n} ℤ (adjoin_root $ polynomial.cyclotomic n ℤ) :=
{ exists_prim_root := λ a ha,
  begin
    obtain rfl : a = n := ha,
    use adjoin_root.root _,
    sorry,
    --rw ←polynomial.is_root_cyclotomic_iff,
    -- I want to get `char_zero` automatically - surely quotienting by a pos-degree poly
    -- preserves characteristic, but I haven't given it too much thought (my idea: if you have
    -- an ideal of the form `(p)`, then all polys have degree ≥ `p`'s (bar `0`))
  end,
  adjoin_roots := sorry }

example {K L M} [comm_ring K] [comm_ring L] [comm_ring M] [algebra K L] [algebra K M]
  {n} [is_cyclotomic_extension {n} K L] [is_cyclotomic_extension {n} K M] : L ≃ₐ[K] M :=
begin
  sorry
end
