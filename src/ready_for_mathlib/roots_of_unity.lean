import ring_theory.roots_of_unity

section comm_monoid

variables {M : Type*} [comm_monoid M]

@[nontriviality] lemma is_primitive_root.of_subsingleton [subsingleton M] (x : M) :
  is_primitive_root x 1 :=
⟨subsingleton.elim _ _, λ _ _, one_dvd _⟩

lemma is_primitive_root.order_of (ζ : M) :
  is_primitive_root ζ (order_of ζ) :=
⟨pow_order_of_eq_one ζ, λ l, order_of_dvd_of_pow_eq_one⟩

lemma is_primitive_root.unique {n m : ℕ} {ζ : M}
  (hn : is_primitive_root ζ n) (hm : is_primitive_root ζ m) : n = m :=
begin
  wlog hnm : n ≤ m,
  rcases hnm.eq_or_lt with rfl | hnm,
  { refl },
  rcases n.eq_zero_or_pos with rfl | hn',
  { exact (zero_dvd_iff.mp $ hn.dvd_of_pow_eq_one m hm.pow_eq_one).symm },
  exact absurd hn.pow_eq_one (hm.pow_ne_one_of_pos_of_lt hn' hnm)
end

lemma is_primitive_root.eq_order_of {n : ℕ} {ζ : M}
  (h : is_primitive_root ζ n) : n = order_of ζ :=
h.unique (is_primitive_root.order_of ζ)

-- equivalent statement for n : ℕ availab,e but too lazy
lemma is_primitive_root_iff {n : ℕ+} (ζ : M) :
  is_primitive_root ζ n ↔ ζ ^ (n : ℕ) = 1 ∧ ∀ l : ℕ, 0 < l → l < n → ζ ^ l ≠ 1 :=
begin
  refine ⟨λ h, ⟨h.pow_eq_one, λ l hl' hl, _⟩, λ ⟨hζ, hl⟩, is_primitive_root.mk_of_lt ζ n.pos hζ hl⟩,
  rw h.eq_order_of at hl,
  exact pow_ne_one_of_lt_order_of' hl'.ne' hl,
end

lemma is_not_primitive_root_iff {n : ℕ} (ζ : M) :
  ¬ is_primitive_root ζ n ↔ order_of ζ ≠ n :=
⟨λ h hn, h $ hn ▸ is_primitive_root.order_of ζ,
 λ h hn, h.symm $ hn.unique $ is_primitive_root.order_of ζ⟩

end comm_monoid

section comm_monoid_with_zero

variables {M₀ : Type*} [comm_monoid_with_zero M₀]

lemma is_primitive_root.zero [nontrivial M₀] :
  is_primitive_root (0 : M₀) 0 :=
⟨pow_zero 0, λ l hl, by simpa [zero_pow_eq, show ∀ p, ¬p → false ↔ p, from @not_not] using hl⟩

end comm_monoid_with_zero

section comm_semiring

variables {R S : Type*} [comm_semiring R] [comm_semiring S] {f : R →+* S}

lemma is_primitive_root.of_injective (hf : function.injective f) {x : R} {n : ℕ}
  (hx : is_primitive_root x n) : is_primitive_root (f x) n :=
{ pow_eq_one := by rw [←f.map_pow, hx.pow_eq_one, f.map_one],
  dvd_of_pow_eq_one := begin
    rw hx.eq_order_of,
    intros l hl,
    rw [←f.map_pow, ←f.map_one] at hl,
    exact order_of_dvd_of_pow_eq_one (hf hl)
  end }

lemma is_primitive_root.of_injective'(hf : function.injective f) {x : R} {n : ℕ}
  (hx : is_primitive_root (f x) n) : is_primitive_root x n :=
{ pow_eq_one := by { apply_fun f, rw [f.map_pow, f.map_one, hx.pow_eq_one] },
  dvd_of_pow_eq_one := begin
    rw hx.eq_order_of,
    intros l hl,
    apply_fun f at hl,
    rw [f.map_pow, f.map_one] at hl,
    exact order_of_dvd_of_pow_eq_one hl
  end }

lemma is_primitive_root.injective_iff (hf : function.injective f) {x : R} {n : ℕ} :
  is_primitive_root x n ↔ is_primitive_root (f x) n :=
⟨λ h, h.of_injective hf, λ h, h.of_injective' hf⟩

end comm_semiring
