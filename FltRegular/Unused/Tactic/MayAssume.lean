import Mathlib.Tactic.Default
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.SlimCheck

/-
Example:

lemma ex (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  may_assume h : a ≤ b,
  {
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c)
  -- (this : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b), a + b < c)
  -- ⊢ a + b < c

  },
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b)
  -- ⊢ a + b < c

end

-/
/-
Example:

lemma ex (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  may_assume h : a ≤ b,
  {
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c)
  -- (this : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b), a + b < c)
  -- ⊢ a + b < c

  },
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b)
  -- ⊢ a + b < c

end

-/
/- lemma ex (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  have : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (this : ∀ (a' b' c' : ℕ) (hab : a'^2 + b'^2 < c') (h : a' ≤ b'), a' + b' < c'),
   a + b < c,
  { clear_except this,
    intros,
    -- state here is
    -- (a b c : ℕ) (hab : a^2 + b^2 < c)
    -- (this : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b), a + b < c)
    -- ⊢ a + b < c
    cases le_total a b; specialize this _ _ c _ h,
    assumption,
    assumption,
    rw add_comm,
    assumption,
    rw add_comm,
    assumption, },
  apply this a b c hab,
  clear_except,
  intros a b c hab h,
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b)
  -- ⊢ a + b < c
  admit,

end -/
/- lemma ex (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  have : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (this : ∀ (a' b' c' : ℕ) (hab : a'^2 + b'^2 < c') (h : a' ≤ b'), a' + b' < c'),
   a + b < c,
  { clear_except this,
    intros,
    -- state here is
    -- (a b c : ℕ) (hab : a^2 + b^2 < c)
    -- (this : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b), a + b < c)
    -- ⊢ a + b < c
    cases le_total a b; specialize this _ _ c _ h,
    assumption,
    assumption,
    rw add_comm,
    assumption,
    rw add_comm,
    assumption, },
  apply this a b c hab,
  clear_except,
  intros a b c hab h,
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b)
  -- ⊢ a + b < c
  admit,

end -/
namespace Tactic.Interactive

open Tactic Expr

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- auxiliary function for `apply_under_n_pis` -/
private unsafe def insert_under_n_pis_aux (na : Name) (ty : expr) : ℕ → ℕ → expr → expr
  | n, 0, bd => expr.pi na BinderInfo.default ty (bd.lift_vars 0 1)
  | n, k + 1, expr.pi nm bi tp bd =>
    expr.pi nm BinderInfo.default tp (insert_under_n_pis_aux (n + 1) k bd)
  | n, k + 1, t => insert_under_n_pis_aux n 0 t

/-- Assumes `pi_expr` is of the form `Π x1 ... xn xn+1..., _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
unsafe def insert_under_n_pis (na : Name) (ty : expr) (pi_expr : expr) (n : ℕ) : expr :=
  insert_under_n_pis_aux na ty 0 n pi_expr

/-- Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
unsafe def insert_under_pis (na : Name) (ty : expr) (pi_expr : expr) : expr :=
  insert_under_n_pis na ty pi_expr pi_expr.pi_arity

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def may_assume (h : parse ident ?) (q₁ : parse (tk ":" *> texpr))
    (wi : parse (tk "with" *> ident)?) (ot : parse (tk "else")?) : tactic Unit :=
  let h := h.getD `this
  let wi := wi.getD `h_red
  focus1 do
    let ls ← local_context
    let q₂ ← to_expr q₁
    let g ← get_goal
    let ⟨n, g⟩ ← goal_of_mvar g
    assert `h_red (insert_under_pis h (q₂ (ls local_uniq_name)) g)
    -- s ← get_local wi,
        -- let t : ident := wi,
        focus1
        sorry
    swap
    if ot then focus1 sorry else skip

end Tactic.Interactive

/- lemma ex' (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  may_assume h : a ≤ b,
  { cases le_total a b; specialize h_red _ _ c _ h,
    assumption,
    assumption,
    rw add_comm,
    assumption,
    rw add_comm,
    assumption, },
admit
end -/
namespace Tactic

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
unsafe def doneif (h : parse ident ?) (t : parse (tk ":" *> texpr))
    (revert :
      parse (tk "generalizing" *> (none <$ tk "*" <|> some <$> ident*) <|> pure (some []))) :
    tactic Unit := do
  let h := h.getD `this
  let t ← i_to_expr ``(($(t) : Sort _))
  let (num_generalized, goal) ←
    retrieve do
        assert_core h t
        swap
        let num_generalized ←
          match revert with
            | none => revert_all
            | some revert => revert.mapM tactic.get_local >>= revert_lst
        let goal ← target
        return (num_generalized, goal)
  tactic.assert h goal
  let goal ← target
  (take_pi_args num_generalized goal).reverse.mapM' fun h =>
      try (tactic.get_local h >>= tactic.clear)
  intron (num_generalized + 1)

unsafe def wlog' (h : parse ident ?) (t : parse (tk ":" *> texpr)) : tactic Unit :=
  doneif h t none >> swap

end Interactive

end Tactic

theorem div_pow''' {a b : ℕ} (n : ℕ) (h : b ∣ a) : (a / b) ^ n = a ^ n / b ^ n :=
  by
  by_cases hb : b = 0
  · simp only [hb, zero_dvd_iff, eq_self_iff_true, Nat.div_zero] at *
    rw [h]
    by_cases hn : n = 0
    simp only [hn, Nat.lt_one_iff, Nat.div_self, pow_zero]
    rw [zero_pow (pos_iff_ne_zero.mpr hn)]
    simp
  have hb : 0 < b := pos_iff_ne_zero.mpr hb
  -- have : 0 < b := by library_search,
  rcases h with ⟨h_w, rfl⟩
  rw [mul_comm, mul_pow, Nat.mul_div_cancel h_w hb, Nat.mul_div_cancel (h_w ^ n) (pow_pos hb n)]

/-
lemma fermat (a b c n : ℕ) (hab : a^n + b^n = c^n) : a * b * c = 0 :=
begin
  may_assume h : a.coprime b with h_red else,
  { use [a / a.gcd b, b / a.gcd b, c / a.gcd b, n],
    simp,
    push_neg,
    split,
    rw div_pow''',
    rw div_pow''',
    rw div_pow''',
    admit,
    admit,
    exact nat.gcd_dvd_right a b,
    exact nat.gcd_dvd_left a b,
    split,
    refine nat.coprime_div_gcd_div_gcd _,
    contrapose h_red,
    simp at h_red,
    simp [h_red],
    split,
    split,
    simp,
    rw [nat.div_eq_zero_iff],
    simp,
    refine nat.le_of_dvd _ _,
    admit,
    exact nat.gcd_dvd_left a b,
    admit,
    admit,
    admit, },
  { admit },
end -/
/- lemma test (a b : ℕ) : (a - b) * (b - a) = 0 :=
begin
  may_assume h : a ≤ b with h_red else,
  { simp,
    admit, },
  { admit },
end

lemma fermat' (a b c d n : ℕ) (hab : a^n + b^n = c^n) (hd : d^2 = 4) : a * b * c = 0 :=
begin
  wlog' h : a.coprime b,
  { admit, },
  { admit },
end -/
