import tactic
import data.nat.basic
import tactic.slim_check

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

lemma ex (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
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
  sorry,

end

namespace tactic.interactive
open tactic expr

setup_tactic_parser

/-- auxiliary function for `apply_under_n_pis` -/
private meta def insert_under_n_pis_aux (na : name) (ty : expr) : ℕ → ℕ → expr → expr
| n 0 bd := expr.pi na binder_info.default ty (bd.lift_vars 0 1)
| n (k+1) (expr.pi nm bi tp bd) :=
  expr.pi nm binder_info.default tp (insert_under_n_pis_aux (n+1) k bd)
| n (k+1) t := insert_under_n_pis_aux n 0 t
/--
Assumes `pi_expr` is of the form `Π x1 ... xn xn+1..., _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def insert_under_n_pis (na : name) (ty : expr) (pi_expr : expr) (n : ℕ) : expr :=
insert_under_n_pis_aux na ty 0 n (pi_expr)

/--
Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def insert_under_pis (na : name) (ty : expr) (pi_expr : expr) : expr :=
insert_under_n_pis na ty pi_expr pi_expr.pi_arity

meta def may_assume (h : parse ident?) (q₁ : parse (tk ":" *> texpr))
  (wi : parse (tk "with" *> ident)?) (ot : parse (tk "else")?)
  : tactic unit :=
let h := h.get_or_else `this,
wi := wi.get_or_else `h_red in
focus1 $ do
  ls ← local_context,
  q₂ ← to_expr q₁,
  g ← get_goal,
  ⟨n,g⟩ ← goal_of_mvar g,
  assert `h_red (insert_under_pis h (q₂.abstract_locals (ls.map local_uniq_name)) g),
  -- s ← get_local wi,
  -- let t : ident := wi,
  focus1 `[clear_except h_red, intros],
  swap,
  if ot.is_some then focus1 `[contrapose! h_red] else skip

end tactic.interactive

lemma ex' (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  may_assume h : a ≤ b,
  { cases le_total a b; specialize h_red _ _ c _ h,
    assumption,
    assumption,
    rw add_comm,
    assumption,
    rw add_comm,
    assumption, },
sorry
end
namespace tactic

meta def take_pi_args : nat → expr → list name
| (n+1) (expr.pi h _ _ e) := h :: take_pi_args n e
| _ _ := []

namespace interactive
setup_tactic_parser

meta def doneif (h : parse ident?) (t : parse (tk ":" *> texpr))
  (revert : parse (
    (tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure (some []))) :
  tactic unit := do
  let h := h.get_or_else `this,
  t ← i_to_expr ``(%%t : Sort*),
  (num_generalized, goal) ← retrieve (do
    assert_core h t, swap,
    num_generalized ← match revert with
    | none := revert_all
    | some revert := revert.mmap tactic.get_local >>= revert_lst
    end,
    goal ← target,
    return (num_generalized, goal)),
  tactic.assert h goal,
  goal ← target,
  (take_pi_args num_generalized goal).reverse.mmap' $ λ h,
    try (tactic.get_local h >>= tactic.clear),
  intron (num_generalized + 1)

meta def wlog' (h : parse ident?) (t : parse (tk ":" *> texpr)) : tactic unit :=
doneif h t none >> swap

end interactive
end tactic

lemma div_pow {a b : ℕ} (n : ℕ) (h : b ∣ a) : (a / b) ^ n = a ^ n / b ^ n :=
begin
  by_cases hb : b = 0,
  { simp only [hb, zero_dvd_iff, eq_self_iff_true, nat.div_zero] at *,
    rw h,
    by_cases hn : n = 0,
    simp only [hn, nat.lt_one_iff, nat.div_self, pow_zero],
    rw zero_pow (pos_iff_ne_zero.mpr hn),
    simp },
  have hb : 0 < b := pos_iff_ne_zero.mpr hb,
  -- have : 0 < b := by library_search,
  rcases h with ⟨h_w, rfl⟩,
  rw [mul_comm, mul_pow, nat.mul_div_cancel h_w hb, nat.mul_div_cancel (h_w ^ n) (pow_pos hb n)],
end

lemma fermat (a b c n : ℕ) (hab : a^n + b^n = c^n) : a * b * c = 0 :=
begin
  may_assume h : a.coprime b with h_red else,
  { use [a / a.gcd b, b / a.gcd b, c / a.gcd b, n],
    simp,
    push_neg,
    split,
    rw div_pow,
    rw div_pow,
    rw div_pow,
    sorry,
    sorry,
    exact nat.gcd_dvd_right a b,
    exact nat.gcd_dvd_left a b,
    split,
    refine nat.coprime_div_gcd_div_gcd _,
    contrapose h_red,
    simp at h_red,
    rw nat.gcd_eq_zero_iff at h_red,
    simp [h_red],
    split,
    split,
    simp,
    rw [nat.div_eq_zero_iff],
    simp,
    refine nat.le_of_dvd _ _,
    sorry,
    exact nat.gcd_dvd_left a b,
    sorry,
    sorry,
    sorry, },
  { sorry },
end

lemma test (a b : ℕ) : (a - b) * (b - a) = 0 :=
begin
  may_assume h : a ≤ b with h_red else,
  { simp,
    sorry, },
  { sorry },
end

lemma fermat' (a b c d n : ℕ) (hab : a^n + b^n = c^n) (hd : d^2 = 4) : a * b * c = 0 :=
begin
  wlog' h : a.coprime b,
  { sorry, },
  { sorry },
end
