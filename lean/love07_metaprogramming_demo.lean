import .love05_inductive_predicates_demo


/-! # LoVe Demo 7: Metaprogramming

Users can extend Lean with custom monadic tactics and tools. This kind of
programming—programming the prover—is called metaprogramming.

Lean's metaprogramming framework uses mostly the same notions and syntax as
Lean's input language itself.

Abstract syntax trees __reflect__ internal data structures, e.g., for
expressions (terms).

The prover's C++ internals are exposed through Lean interfaces, which we can
use for accessing the current context and goal, unifying expressions, querying
and modifying the environment, and setting attributes (e.g., `@[simp]`).

Most of Lean's predefined tactics are implemented in Lean (and not in C++).

Example applications:

* proof goal transformations;
* heuristic proof search;
* decision procedures;
* definition generators;
* advisor tools;
* exporters;
* ad hoc automation.

Advantages of Lean's metaprogramming framework:

* Users do not need to learn another programming language to write
  metaprograms; they can work with the same constructs and notation used to
  define ordinary objects in the prover's library.

* Everything in that library is available for metaprogramming purposes.

* Metaprograms can be written and debugged in the same interactive environment,
  encouraging a style where formal libraries and supporting automation are
  developed at the same time. -/


set_option pp.beta true

namespace LoVe


/-! ## Tactics and Tactic Combinators

When programming our own tactics, we often need to repeat some actions on
several goals, or to recover if a tactic fails. Tactic combinators help in such
case.

`repeat` applies its argument repeatedly on all (sub…sub)goals until it cannot
be applied any further. -/

lemma repeat_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  repeat { apply even.add_two },
  repeat { sorry }
end

/-! The "orelse" combinator `<|>` tries its first argument and applies its
second argument in case of failure. -/

lemma repeat_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  repeat {
    apply even.add_two
    <|> apply even.zero },
  repeat { sorry }
end

/-! `iterate` works repeatedly on the first goal until it fails; then it
stops. -/

lemma iterate_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  iterate {
    apply even.add_two
    <|> apply even.zero },
  repeat { sorry }
end

/-! `all_goals` applies its argument exactly once to each goal. It succeeds only
if the argument succeeds on **all** goals. -/

lemma all_goals_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  all_goals { apply even.add_two },   -- fails
  repeat { sorry }
end

/-! `try` transforms its argument into a tactic that never fails. -/

lemma all_goals_try_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  all_goals { try { apply even.add_two } },
  repeat { sorry }
end

/-! `any_goals` applies its argument exactly once to each goal. It succeeds
if the argument succeeds on **any** goal. -/

lemma any_goals_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  any_goals { apply even.add_two },
  repeat { sorry }
end

/-! `solve1` transforms its argument into an all-or-nothing tactic. If the
argument does not prove the goal, `solve1` fails. -/

lemma any_goals_solve1_repeat_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  any_goals { solve1 { repeat {
    apply even.add_two
    <|> apply even.zero } } },
  repeat { sorry }
end

/-! The combinators `repeat`, `iterate`, `all_goals`, and `any_goals` can easily
lead to infinite looping: -/

/-!
lemma repeat_not_example :
  ¬ even 1 :=
begin
  repeat { apply not.intro },
  sorry
end
-/

/-! Let us start with the actual metaprogramming, by coding a custom tactic. The
tactic embodies the behavior we hardcoded in the `solve1` example above: -/

meta def intro_and_even : tactic unit :=
do
  tactic.repeat (tactic.applyc ``and.intro),
  tactic.any_goals (tactic.solve1 (tactic.repeat
    (tactic.applyc ``even.add_two
     <|> tactic.applyc ``even.zero)))

/-! The `meta` keyword makes it possible for the function to call other
metafunctions. The `do` keyword enters a monad, and the `<|>` operator is the
"orelse" operator of alternative monads.

Any executable Lean definition can be used as a metaprogram. In addition, we can
put `meta` in front of a definition to indicate that is a metadefinition. Such
definitions need not terminate but cannot be used in non-`meta` contexts.

Let us apply our custom tactic: -/

lemma any_goals_solve1_repeat_orelse_example₂ :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  intro_and_even,
  repeat { sorry }
end


/-! ## The Metaprogramming Monad

Tactics have access to

* the list of **goals** as metavariables (each metavariables has a type and a
  local context (hypothesis); they can optionally be instantiated);

* the **elaborator** (to elaborate expressions and compute their type);

* the **environment**, containing all declarations and inductive types;

* the **attributes** (e.g., the list of `@[simp]` rules).

The tactic monad is an alternative monad, with `fail` and `<|>`. Tactics can
also produce trace messages. -/

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


/-! ## Names, Expressions, Declarations, and Environments

The metaprogramming framework is articulated around five main types:

* `tactic` manages the proof state, the global context, and more;

* `name` represents a structured name (e.g., `x`, `even.add_two`);

* `expr` represents an expression (a term) as an abstract syntax tree;

* `declaration` represents a constant declaration, a definition, an axiom, or a
  lemma;

* `environment` stores all the declarations and notations that make up the
  global context. -/

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

/-! We can create literal expressions conveniently using backticks and
parentheses:

* Expressions with a single backtick must be fully elaborated.

* Expressions with two backticks are __pre-expressions__: They may contain some
  holes to be filled in later, based on some context.

* Expressions with three backticks are pre-expressions without name checking. -/

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

/-! We can also create literal names with backticks:

* Names with a single backtick, `n, are not checked for existence.

* Names with two backticks, ``n, are resolved and checked. -/

run_cmd tactic.trace `and.intro
run_cmd tactic.trace `intro_and_even
run_cmd tactic.trace `seattle.washington

run_cmd tactic.trace ``and.intro
run_cmd tactic.trace ``intro_and_even
run_cmd tactic.trace ``seattle.washington   -- fails

/-! __Antiquotations__ embed an existing expression in a larger expression. They
are announced by the prefix `%%` followed by a name from the current context.
Antiquotations are available with one, two, and three backticks: -/

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

/-! The `environment` type is presented as an abstract type, equipped with some
operations to query and modify it. The `environment.fold` metafunction iterates
over all declarations making up the environment. -/

run_cmd do
  env ← tactic.get_env,
  tactic.trace (environment.fold env 0 (λdecl n, n + 1))


/-! ## First Example: A Conjuction-Destructing Tactic

We define a `destruct_and` tactic that automates the elimination of `∧` in
premises, automating proofs such as these: -/

lemma abcd_a (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  a :=
and.elim_left h

lemma abcd_b (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b :=
and.elim_left (and.elim_left (and.elim_right h))

lemma abcd_bc (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ c :=
and.elim_left (and.elim_right h)

/-! Our tactic relies on a helper metafunction, which takes as argument the
hypothesis `h` to use as an expression rather than as a name: -/

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

/-! Let us check that our tactic works: -/

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


/-! ## Second Example: A Provability Advisor

Next, we implement a `prove_direct` tool that traverses all lemmas in the
database and checks whether one of them can be used to prove the current goal. A
similar tactic is available in `mathlib` under the name `library_search`. -/

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

/-! As a small refinement, we propose a version of `prove_direct` that also
looks for equalities stated in symmetric form. -/

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


/-! ## A Look at Two Predefined Tactics

Quite a few of Lean's predefined tactics are implemented as metaprograms and
not in C++. We can find these definitions by clicking the name of a construct
in Visual Studio Code while holding the control or command key. -/

#check tactic.intro
#check tactic.assumption

end LoVe
