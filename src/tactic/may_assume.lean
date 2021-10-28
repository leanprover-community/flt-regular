import tactic

#check tactic.interactive.suffices
#check tactic.interactive.extract_goal


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

#check tactic.interactive.have
setup_tactic_parser
#print prefix pexpr
#check pexpr.mk_explicit
#check expr.erase_annotations
#check expr.pi
/-- auxiliary function for `apply_under_n_pis` -/
private meta def insert_under_n_pis_aux (na : name) (ty : pexpr) (ine : pexpr) : ℕ → ℕ → pexpr → pexpr
| n 0 bd := let naa : expr := (expr.const na []) in
  -- let vars := ((list.range n).reverse.map (@expr.var ff)),
  --     bd := vars.foldl expr.app arg.mk_explicit in
  ``(Π (_ : %%ty), %%ine)
| n (k+1) (expr.pi nm bi tp bd) :=
  let x := (insert_under_n_pis_aux (n+1) k bd) in expr.pi nm binder_info.default (to_pexpr tp : pexpr) x
| n (k+1) t := insert_under_n_pis_aux n 0 t
/--
Assumes `pi_expr` is of the form `Π x1 ... xn xn+1..., _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def insert_under_n_pis (na : name) (ty : pexpr) (pi_expr : expr) (n : ℕ) : pexpr :=
insert_under_n_pis_aux na ty (to_pexpr ((pi_expr.nth_binding_body n))).erase_annotations 0 n (to_pexpr pi_expr).erase_annotations
-- #check as_is
-- set_option pp.all true
run_cmd (do
  -- trace (insert_under_n_pis `h ``(1 = 1) `(∀ (a b : ℕ), 2 = 2))
  trace (insert_under_n_pis `h ```(b = c) `(∀ (a b : ℕ), a = b) 2)
  )

/--
Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def insert_under_pis (na : name) (ty : pexpr) (pi_expr : expr) : pexpr :=
insert_under_n_pis na ty pi_expr pi_expr.pi_arity

meta def get_proof_state : tactic proof_state :=
do gs ← get_goals,
   gs.mmap $ λ g, do
     ⟨n,g⟩ ← goal_of_mvar g,
     g ← gs.mfoldl (λ g v, do
       g ← kabstract g v reducible ff,
       pure $ pi `goal binder_info.default `(true) g ) g,
     pure (n,g)
meta def may_assume --(print_use : parse $ tt <$ tk "!" <|> pure ff)
(h : parse ident?) (q₁ : parse (tk ":" *> texpr))
  -- (n : parse_) -- (vs : parse (tk "with" *> ident*)?)
  : tactic unit :=
let h := h.get_or_else `this in
focus1 $ do --tgt ← target,
ls ← local_context,
trace ls,
-- mk_mvar,
tgt ← target >>= instantiate_mvars,
-- q₂,l⟩ ←
-- with_local_goals [] (to_expr q₁),
-- trace q₂,
-- trace "tgt",
-- trace tgt,
-- tgt ← pis (ls) tgt,
-- trace "tgt",
-- trace tgt,
g ← get_goal,
⟨n,g⟩ ← goal_of_mvar g,
trace g,
-- q ← to_expr q₁,
trace q₁,
trace tgt,
trace (insert_under_pis h q₁ g),
ne ←
(to_expr (insert_under_pis h q₁ g)),
-- trace ne,
-- assert `eh ne,
-- tactic.apply `(`eh),
-- set_goal,
skip
end tactic.interactive

lemma ex' (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  may_assume h : a ≤ b,
  -- have : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (this : ∀ (a' b' c' : ℕ) (hab : a'^2 + b'^2 < c') (h : a' ≤ b'), a' + b' < c'),
  --  a + b < c,
  sorry; {
    -- clear_except this,
    -- intros,
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
  -- apply this a b c hab,
  -- clear_except,
  -- intros a b c hab h,
  -- state here is
  -- (a b c : ℕ) (hab : a^2 + b^2 < c) (h : a ≤ b)
  -- ⊢ a + b < c
  -- sorry,

end
