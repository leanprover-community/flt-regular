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
open tactic

#check tactic.interactive.have
setup_tactic_parser
meta def may_assume --(print_use : parse $ tt <$ tk "!" <|> pure ff)
(h : parse ident?) (q₁ : parse (tk ":" *> texpr)?)
  -- (n : parse_) -- (vs : parse (tk "with" *> ident*)?)
  : tactic unit :=
do tgt ← target,
  --  solve_aux tgt $ do {
  --    ((cxt₀,cxt₁,ls,tgt),_) ← solve_aux tgt $ do {
  --        vs.mmap clear_except,
  --        ls ← local_context,
  --        ls ← ls.mfilter $ succeeds ∘ is_local_def,
  --        n ← revert_lst ls,
  --        (c₀,c₁) ← partition_vars,
  --        tgt ← target,
  --        ls ← intron' n,
  --        pure (c₀,c₁,ls,tgt) },
  --    is_prop ← is_prop tgt,
  --    let title := match n, is_prop with
  --                 | none, _ := to_fmt "example"
  --                 | (some n), tt := format!"lemma {n}"
  --                 | (some n), ff := format!"def {n}"
  --                 end,
  --    cxt₀ ← compact_decl cxt₀ >>= list.mmap format_binders,
  --    cxt₁ ← compact_decl cxt₁ >>= list.mmap format_binders,
  --    stmt ← pformat!"{tgt} :=",
  --    let fmt :=
  --      format.group $ format.nest 2 $
  --        title ++ cxt₀.foldl (λ acc x, acc ++ format.group (format.line ++ x)) "" ++
  --        format.join (list.map (λ x, format.line ++ x) cxt₁) ++ " :" ++
  --        format.line ++ stmt,
  --    trace $ fmt.to_string $ options.mk.set_nat `pp.width 80,
  --    let var_names := format.intercalate " " $ ls.map (to_fmt ∘ local_pp_name),
  --    let call_intron := if ls.empty
  --                    then to_fmt ""
  --                    else format!"\n  intros {var_names},",
  --    trace!"begin{call_intron}\n  admit,\nend\n" },
   skip
end tactic.interactive

lemma ex' (a b c : ℕ) (hab : a^2 + b^2 < c) : a + b < c :=
begin
  may_assume h : a ≤ b,
  -- have : ∀ (a b c : ℕ) (hab : a^2 + b^2 < c) (this : ∀ (a' b' c' : ℕ) (hab : a'^2 + b'^2 < c') (h : a' ≤ b'), a' + b' < c'),
  --  a + b < c,
  sorry;{
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

end
