import .love05_inductive_predicates_demo


/-! # LoVe Demo 7: Metaprogramming -/


set_option pp.beta true

namespace LoVe


/-! ## Tactics and Tactic Combinators -/

lemma repeat_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  repeat { apply even.add_two },
  repeat { sorry }
end

lemma repeat_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  repeat {
    apply even.add_two
    <|> apply even.zero },
  repeat { sorry }
end

lemma iterate_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  iterate {
    apply even.add_two
    <|> apply even.zero },
  repeat { sorry }
end

lemma all_goals_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  all_goals { apply even.add_two },   -- fails
  repeat { sorry }
end

lemma all_goals_try_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  all_goals { try { apply even.add_two } },
  repeat { sorry }
end

lemma any_goals_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  any_goals { apply even.add_two },
  repeat { sorry }
end

lemma any_goals_solve1_repeat_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  any_goals { solve1 { repeat {
    apply even.add_two
    <|> apply even.zero } } },
  repeat { sorry }
end

/-!
lemma repeat_not_example :
  ¬ even 1 :=
begin
  repeat { apply not.intro },
  sorry
end
-/

meta def intro_and_even : tactic unit :=
do
  tactic.repeat (tactic.applyc ``and.intro),
  tactic.any_goals (tactic.solve1 (tactic.repeat
    (tactic.applyc ``even.add_two
     <|> tactic.applyc ``even.zero)))

lemma any_goals_solve1_repeat_orelse_example₂ :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  intro_and_even,
  repeat { sorry }
end


/-! ## The Metaprogramming Monad -/

lemma even_14 :
  even 14 :=
by do
  tactic.trace "Proving evenness …",
  intro_and_even

meta def hello_then_intro_and_even : tactic unit :=
do
  tactic.trace "Proving evenness …",
  intro_and_even

lemma even_16 :
  even 16 :=
by hello_then_intro_and_even

run_cmd tactic.trace "Hello, Metaworld!"

meta def trace_goals : tactic unit :=
do
  tactic.trace "local context:",
  ctx ← tactic.local_context,
  tactic.trace ctx,
  tactic.trace "target:",
  P ← tactic.target,
  tactic.trace P,
  tactic.trace "all missing proofs:",
  Hs ← tactic.get_goals,
  tactic.trace Hs,
  τs ← list.mmap tactic.infer_type Hs,
  tactic.trace τs

lemma even_18_and_even_20 (α : Type) (a : α) :
  even 18 ∧ even 20 :=
by do
  tactic.applyc ``and.intro,
  trace_goals,
  intro_and_even

lemma triv_imp (a : Prop) (h : a) :
  a :=
by do
  h ← tactic.get_local `h,
  tactic.trace "h:",
  tactic.trace h,
  tactic.trace "raw h:",
  tactic.trace (expr.to_raw_fmt h),
  tactic.trace "type of h:",
  τ ← tactic.infer_type h,
  tactic.trace τ,
  tactic.trace "type of type of h:",
  υ ← tactic.infer_type τ,
  tactic.trace υ,
  tactic.apply h

meta def exact_list : list expr → tactic unit
| []        := tactic.fail "no matching expression found"
| (h :: hs) :=
  do {
    tactic.trace "trying",
    tactic.trace h,
    tactic.exact h }
  <|> exact_list hs

meta def hypothesis : tactic unit :=
do
  hs ← tactic.local_context,
  exact_list hs

lemma p_a_of_p_a {α : Type} {p : α → Prop} {a : α} (h : p a) :
  p a :=
by hypothesis


/-! ## Names, Expressions, Declarations, and Environments -/

#print expr

#check expr tt  -- elaborated expressions
#check expr ff  -- unelaborated expressions (pre-expressions)

#print name

#check (expr.const `ℕ [] : expr)
#check expr.sort level.zero  -- Sort 0, i.e., Prop
#check expr.sort (level.succ level.zero)
  -- Sort 1, i.e., Type
#check expr.var 0  -- bound variable with De Bruijn index 0
#check (expr.local_const `uniq_name `pp_name binder_info.default
  `(ℕ) : expr)
#check (expr.mvar `uniq_name `pp_name `(ℕ) : expr)
#check (expr.pi `pp_name binder_info.default `(ℕ)
  (expr.sort level.zero) : expr)
#check (expr.lam `pp_name binder_info.default `(ℕ)
  (expr.var 0) : expr)
#check expr.elet
#check expr.macro

run_cmd do
  let e : expr := `(list.map (λn : ℕ, n + 1) [1, 2, 3]),
  tactic.trace e

run_cmd do
  let e : expr := `(list.map _ [1, 2, 3]),   -- fails
  tactic.trace e

run_cmd do
  let e₁ : pexpr := ``(list.map (λn, n + 1) [1, 2, 3]),
  let e₂ : pexpr := ``(list.map _ [1, 2, 3]),
  tactic.trace e₁,
  tactic.trace e₂

run_cmd do
  let e : pexpr := ```(seattle.washington),
  tactic.trace e

run_cmd tactic.trace `and.intro
run_cmd tactic.trace `intro_and_even
run_cmd tactic.trace `seattle.washington

run_cmd tactic.trace ``and.intro
run_cmd tactic.trace ``intro_and_even
run_cmd tactic.trace ``seattle.washington   -- fails

run_cmd do
  let x : expr := `(2 : ℕ),
  let e : expr := `(%%x + 1),
  tactic.trace e

run_cmd do
  let x : expr  := `(@id ℕ),
  let e : pexpr := ``(list.map %%x),
  tactic.trace e

run_cmd do
  let x : expr  := `(@id ℕ),
  let e : pexpr := ```(a _ %%x),
  tactic.trace e

lemma one_add_two_eq_three :
  1 + 2 = 3 :=
by do
  `(%%a + %%b = %%c) ← tactic.target,
  tactic.trace a,
  tactic.trace b,
  tactic.trace c,
  `(@eq %%α %%l %%r) ← tactic.target,
  tactic.trace α,
  tactic.trace l,
  tactic.trace r,
  tactic.exact `(refl _ : 3 = 3)

#print declaration

run_cmd do
  env ← tactic.get_env,
  tactic.trace (environment.fold env 0 (λdecl n, n + 1))


/-! ## A Conjuction-Destructing Tactic -/

lemma abcd_a (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  a :=
and.elim_left h

lemma abcd_b (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b :=
and.elim_left (and.elim_left (and.elim_right h))

lemma abcd_bc (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ c :=
and.elim_left (and.elim_right h)

meta def destruct_and_helper : expr → tactic unit
| h :=
  do
    t ← tactic.infer_type h,
    match t with
    | `(%%a ∧ %%b) :=
      tactic.exact h
      <|>
      do {
        ha ← tactic.to_expr ``(and.elim_left %%h),
        destruct_and_helper ha }
      <|>
      do {
        hb ← tactic.to_expr ``(and.elim_right %%h),
        destruct_and_helper hb }
    | _            := tactic.exact h
    end

meta def destruct_and (nam : name) : tactic unit :=
do
  h ← tactic.get_local nam,
  destruct_and_helper h

lemma abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
  a :=
by destruct_and `h

lemma abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
  b :=
by destruct_and `h

lemma abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
by destruct_and `h

lemma abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
  a ∧ c :=
by destruct_and `h   -- fails


/-! ## A Provability Advisor -/

meta def is_theorem : declaration → bool
| (declaration.defn _ _ _ _ _ _) := ff
| (declaration.thm _ _ _ _)      := tt
| (declaration.cnst _ _ _ _)     := ff
| (declaration.ax _ _ _)         := tt

meta def get_all_theorems : tactic (list name) :=
do
  env ← tactic.get_env,
  pure (environment.fold env [] (λdecl nams,
    if is_theorem decl then declaration.to_name decl :: nams
    else nams))

meta def prove_with_name (nam : name) : tactic unit :=
do
  tactic.applyc nam
    ({ md := tactic.transparency.reducible, unify := ff }
     : tactic.apply_cfg),
  tactic.all_goals tactic.assumption

meta def prove_direct : tactic unit :=
do
  nams ← get_all_theorems,
  list.mfirst (λnam,
      do
        prove_with_name nam,
        tactic.trace ("directly proved by " ++ to_string nam))
    nams

lemma nat.eq_symm (x y : ℕ) (h : x = y) :
  y = x :=
by prove_direct

lemma nat.eq_symm₂ (x y : ℕ) (h : x = y) :
  y = x :=
by library_search

lemma list.reverse_twice (xs : list ℕ) :
  list.reverse (list.reverse xs) = xs :=
by prove_direct

lemma list.reverse_twice_symm (xs : list ℕ) :
  xs = list.reverse (list.reverse xs) :=
by prove_direct   -- fails

meta def prove_direct_symm : tactic unit :=
prove_direct
<|>
do {
  tactic.applyc `eq.symm,
  prove_direct }

lemma list.reverse_twice₂ (xs : list ℕ) :
  list.reverse (list.reverse xs) = xs :=
by prove_direct_symm

lemma list.reverse_twice_symm₂ (xs : list ℕ) :
  xs = list.reverse (list.reverse xs) :=
by prove_direct_symm


/-! ## A Look at Two Predefined Tactics -/

#check tactic.intro
#check tactic.assumption

end LoVe
