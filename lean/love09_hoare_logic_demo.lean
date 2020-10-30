import .love08_operational_semantics_demo


/- # LoVe Demo 9: Hoare Logic

We review a second way to specify the semantics of a programming language: Hoare
logic. If operational semantics corresponds to an idealized interpreter,
__Hoare logic__ (also called __axiomatic semantics__) corresponds to a verifier.
Hoare logic is particularly convenient to reason about concrete programs. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## First Things First: Formalization Projects

Instead of two of the homework sheets, you can do a verification project, worth
20 points. If you choose to do so, please send your lecturer a message by email
by the end of the week. For a fully successful project, we expect about 200 (or
more) lines of Lean, including definitions and proofs.

Some ideas for projects follow.

Computer science:

* extended WHILE language with static arrays or other features;
* functional data structures (e.g., balanced trees);
* functional algorithms (e.g., bubble sort, merge sort, Tarjan's algorithm);
* compiler from expressions or imperative programs to, e.g., stack machine;
* type systems (e.g., Benjamin Pierce's __Types and Programming Languages__);
* security properties (e.g., Volpano–Smith-style noninterference analysis);
* theory of first-order terms, including matching, term rewriting;
* automata theory;
* normalization of context-free grammars or regular expressions;
* process algebras and bisimilarity;
* soundness and possibly completeness of proof systems (e.g., Genzen's sequent
  calculus, natural deduction, tableaux);
* separation logic;
* verified program using Hoare logic.

Mathematics:

* graphs;
* combinatorics;
* number theory.

Evaluation from 2018–2019:

Q: How did you find the project?

A: Enjoyable.

A: Fun and hard.

A: Good, I think the format was excellent in a way that it gave people the
   chance to do challenging exercises and hand them in incomplete.

A: I really really liked it. I think it's a great way of learning—find
   something you like, dig in it a little, get stuck, ask for help. I wish I
   could do more of that!

A: It was great to have some time to try to work out some stuff you find
   interesting yourself.

A: lots of fun actually!!!

A: Very helpful. It gave the opportunity to spend some more time on a
   particular aspect of the course.


## Hoare Triples

The basic judgments of Hoare logic are often called __Hoare triples__. They have
the form

    `{P} S {Q}`

where `S` is a statement, and `P` and `Q` (called __precondition__ and
__postcondition__) are logical formulas over the state variables.

Intended meaning:

    If `P` holds before `S` is executed and the execution terminates normally,
    `Q` holds at termination.

This is a __partial correctness__ statement: The program is correct if it
terminates normally (i.e., no run-time error, no infinite loop or divergence).

All of these Hoare triples are valid (with respect to the intended meaning):

    `{true} b := 4 {b = 4}`
    `{a = 2} b := 2 * a {a = 2 ∧ b = 4}`
    `{b ≥ 5} b := b + 1 {b ≥ 6}`
    `{false} skip {b = 100}`
    `{true} while i ≠ 100 do i := i + 1 {i = 100}`


## Hoare Rules

The following is a complete set of rules for reasoning about WHILE programs:

    ———————————— Skip
    {P} skip {P}

    ——————————————————— Asn
    {Q[a/x]} x := a {Q}

    {P} S {R}   {R} S' {Q}
    —————————————————————— Seq
    {P} S; S' {Q}

    {P ∧ b} S {Q}   {P ∧ ¬b} S' {Q}
    ——————————————————————————————— If
    {P} if b then S else S' {Q}

    {I ∧ b} S {I}
    ————————————————————————— While
    {I} while b do S {I ∧ ¬b}

    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}

`Q[a/x]` denotes `Q` with `x` replaced by `a`.

In the `While` rule, `I` is called an __invariant__.

Except for `Conseq`, the rules are syntax-driven: by looking at a program, we
see immediately which rule to apply.

Example derivations:

    —————————————————————— Asn   —————————————————————— Asn
    {a = 2} b := a {b = 2}       {b = 2} c := b {c = 2}
    ——————————————————————————————————————————————————— Seq
    {a = 2} b := a; c := b {c = 2}


                     —————————————————————— Asn
    x > 10 → x > 5   {x > 5} y := x {y > 5}   y > 5 → y > 0
    ——————————————————————————————————————————————————————— Conseq
    {x > 10} y := x {y > 0}

Various __derived rules__ can be proved to be correct in terms of the standard
rules. For example, we can derive bidirectional rules for `skip`, `:=`, and
`while`:

    P → Q
    ———————————— Skip'
    {P} skip {Q}

    P → Q[a/x]
    —————————————— Asn'
    {P} x := a {Q}

    {P ∧ b} S {P}   P ∧ ¬b → Q
    —————————————————————————— While'
    {P} while b do S {Q}


## A Semantic Approach to Hoare Logic

We can, and will, define Hoare triples **semantically** in Lean.

We will use predicates on states (`state → Prop`) to represent pre- and
postconditions, following the shallow embedding style. -/

def partial_hoare (P : state → Prop) (S : stmt)
  (Q : state → Prop) : Prop :=
∀s t, P s → (S, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` :=
partial_hoare P S Q

namespace partial_hoare

lemma skip_intro {P} :
  {* P *} stmt.skip {* P *} :=
begin
  intros s t hs hst,
  cases' hst,
  assumption
end

lemma assign_intro (P : state → Prop) {x} {a : state → ℕ} :
  {* λs, P (s{x ↦ a s}) *} stmt.assign x a {* P *} :=
begin
  intros s t P hst,
  cases' hst,
  assumption
end

lemma seq_intro {P Q R S T} (hS : {* P *} S {* Q *})
    (hT : {* Q *} T {* R *}) :
  {* P *} S ;; T {* R *} :=
begin
  intros s t hs hst,
  cases' hst,
  apply hT,
  { apply hS,
    { exact hs },
    { assumption } },
  { assumption }
end

lemma ite_intro {b P Q : state → Prop} {S T}
    (hS : {* λs, P s ∧ b s *} S {* Q *})
    (hT : {* λs, P s ∧ ¬ b s *} T {* Q *}) :
  {* P *} stmt.ite b S T {* Q *} :=
begin
  intros s t hs hst,
  cases' hst,
  { apply hS,
    exact and.intro hs hcond,
    assumption },
  { apply hT,
    exact and.intro hs hcond,
    assumption }
end

lemma while_intro (P : state → Prop) {b : state → Prop} {S}
    (h : {* λs, P s ∧ b s *} S {* P *}) :
  {* P *} stmt.while b S {* λs, P s ∧ ¬ b s *} :=
begin
  intros s t hs hst,
  induction' hst,
  case while_true {
    apply ih_hst_1 P h,
    exact h _ _ (and.intro hs hcond) hst },
  case while_false {
    exact and.intro hs hcond }
end

lemma consequence {P P' Q Q' : state → Prop} {S}
    (h : {* P *} S {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} S {* Q' *} :=
fix s t,
assume hs : P' s,
assume hst : (S, s) ⟹ t,
show Q' t, from
  hq _ (h s t (hp s hs) hst)

lemma consequence_left (P' : state → Prop) {P Q S}
    (h : {* P *} S {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} S {* Q *} :=
consequence h hp (by cc)

lemma consequence_right (Q) {Q' : state → Prop} {P S}
    (h : {* P *} S {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} S {* Q' *} :=
consequence h (by cc) hq

lemma skip_intro' {P Q : state → Prop} (h : ∀s, P s → Q s) :
  {* P *} stmt.skip {* Q *} :=
consequence skip_intro h (by cc)

lemma assign_intro' {P Q : state → Prop} {x} {a : state → ℕ}
    (h : ∀s, P s → Q (s{x ↦ a s})):
  {* P *} stmt.assign x a {* Q *} :=
consequence (assign_intro Q) h (by cc)

lemma seq_intro' {P Q R S T} (hT : {* Q *} T {* R *})
    (hS : {* P *} S {* Q *}) :
  {* P *} S ;; T {* R *} :=
seq_intro hS hT

lemma while_intro' {b P Q : state → Prop} {S}
    (I : state → Prop)
    (hS : {* λs, I s ∧ b s *} S {* I *})
    (hP : ∀s, P s → I s)
    (hQ : ∀s, ¬ b s → I s → Q s) :
  {* P *} stmt.while b S {* Q *} :=
consequence (while_intro I hS) hP (by finish)

/- `finish` applies a combination of techniques, including normalization of
logical connectives and quantifiers, simplification, congruence closure, and
quantifier instantiation. It either fully succeeds or fails. -/

lemma assign_intro_forward (P) {x a} :
  {* P *}
  stmt.assign x a
  {* λs, ∃n₀, P (s{x ↦ n₀}) ∧ s x = a (s{x ↦ n₀}) *} :=
begin
  apply assign_intro',
  intros s hP,
  apply exists.intro (s x),
  simp [*]
end

lemma assign_intro_backward (Q : state → Prop) {x}
    {a : state → ℕ} :
  {* λs, ∃n', Q (s{x ↦ n'}) ∧ n' = a s *}
  stmt.assign x a
  {* Q *} :=
begin
  apply assign_intro',
  intros s hP,
  cases' hP,
  cc
end

end partial_hoare


/- ## First Program: Exchanging Two Variables -/

def SWAP : stmt :=
stmt.assign "t" (λs, s "a") ;;
stmt.assign "a" (λs, s "b") ;;
stmt.assign "b" (λs, s "t")

lemma SWAP_correct (a₀ b₀ : ℕ) :
  {* λs, s "a" = a₀ ∧ s "b" = b₀ *}
  SWAP
  {* λs, s "a" = b₀ ∧ s "b" = a₀ *} :=
begin
  apply partial_hoare.seq_intro',
  apply partial_hoare.seq_intro',
  apply partial_hoare.assign_intro,
  apply partial_hoare.assign_intro,
  apply partial_hoare.assign_intro',
  simp { contextual := tt }
end

lemma SWAP_correct₂ (a₀ b₀ : ℕ) :
  {* λs, s "a" = a₀ ∧ s "b" = b₀ *}
  SWAP
  {* λs, s "a" = b₀ ∧ s "b" = a₀ *} :=
begin
  intros s t hP hstep,
  cases' hstep,
  cases' hstep,
  cases' hstep_1,
  cases' hstep_1_1,
  cases' hstep_1,
  finish
end


/- ## Second Program: Adding Two Numbers -/

def ADD : stmt :=
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "n" (λs, s "n" - 1) ;;
   stmt.assign "m" (λs, s "m" + 1))

lemma ADD_correct (n₀ m₀ : ℕ) :
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *}
  ADD
  {* λs, s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
partial_hoare.while_intro' (λs, s "n" + s "m" = n₀ + m₀)
  begin
    apply partial_hoare.seq_intro',
    { apply partial_hoare.assign_intro },
    { apply partial_hoare.assign_intro',
      simp,
      intros s hnm hnz,
      rw ←hnm,
      cases' s "n",
      { finish },
      { simp [nat.succ_eq_add_one],
        linarith } }
  end
  (by simp { contextual := true })
  (by simp { contextual := true })


/- ## A Verification Condition Generator

__Verification condition generators__ (VCGs) are programs that apply Hoare rules
automatically, producing __verification conditions__ that must be proved by the
user. The user must usually also provide strong enough loop invariants, as an
annotation in their programs.

We can use Lean's metaprogramming framework to define a simple VCG.

Hundreds if not thousands of program verification tools are based on these
principles. Often these are based on an extension called separation logic.

VCGs typically work backwards from the postcondition, using backward rules
(rules stated to have an arbitrary `Q` as their postcondition). This works well
because `Asn` is backward. -/

def stmt.while_inv (I b : state → Prop) (S : stmt) : stmt :=
stmt.while b S

namespace partial_hoare

lemma while_inv_intro {b I Q : state → Prop} {S}
    (hS : {* λs, I s ∧ b s *} S {* I *})
    (hQ : ∀s, ¬ b s → I s → Q s) :
  {* I *} stmt.while_inv I b S {* Q *} :=
while_intro' I hS (by cc) hQ

lemma while_inv_intro' {b I P Q : state → Prop} {S}
    (hS : {* λs, I s ∧ b s *} S {* I *})
    (hP : ∀s, P s → I s) (hQ : ∀s, ¬ b s → I s → Q s) :
  {* P *} stmt.while_inv I b S {* Q *} :=
while_intro' I hS hP hQ

end partial_hoare

meta def vcg : tactic unit :=
do
  t ← tactic.target,
  match t with
  | `({* %%P *} %%S {* _ *}) :=
    match S with
    | `(stmt.skip)            :=
      tactic.applyc
        (if expr.is_mvar P then ``partial_hoare.skip_intro
         else ``partial_hoare.skip_intro')
    | `(stmt.assign _ _)      :=
      tactic.applyc
        (if expr.is_mvar P then ``partial_hoare.assign_intro
         else ``partial_hoare.assign_intro')
    | `(stmt.seq _ _)         :=
      tactic.applyc ``partial_hoare.seq_intro'; vcg
    | `(stmt.ite _ _ _)       :=
      tactic.applyc ``partial_hoare.ite_intro; vcg
    | `(stmt.while_inv _ _ _) :=
      tactic.applyc
        (if expr.is_mvar P then ``partial_hoare.while_inv_intro
         else ``partial_hoare.while_inv_intro');
        vcg
    | _                       :=
      tactic.fail (to_fmt "cannot analyze " ++ to_fmt S)
    end
  | _                        := pure ()
  end

end LoVe

/- Register `vcg` as a proper tactic: -/

meta def tactic.interactive.vcg : tactic unit :=
LoVe.vcg

namespace LoVe


/- ## Second Program Revisited: Adding Two Numbers -/

lemma ADD_correct₂ (n₀ m₀ : ℕ) :
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *}
  ADD
  {* λs, s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
show {* λs, s "n" = n₀ ∧ s "m" = m₀ *}
     stmt.while_inv (λs, s "n" + s "m" = n₀ + m₀)
       (λs, s "n" ≠ 0)
       (stmt.assign "n" (λs, s "n" - 1) ;;
        stmt.assign "m" (λs, s "m" + 1))
     {* λs, s "n" = 0 ∧ s "m" = n₀ + m₀ *}, from
  begin
    vcg; simp { contextual := tt },
    intros s hnm hnz,
    rw ←hnm,
    cases' s "n",
    { finish },
    { simp [nat.succ_eq_add_one],
      linarith }
  end


/- ## Hoare Triples for Total Correctness

__Total correctness__ asserts that the program not only is partially correct but
also that it always terminates normally. Hoare triples for total correctness
have the form

    [P] S [Q]

Intended meaning:

    If `P` holds before `S` is executed, the execution terminates normally and
    `Q` holds in the final state.

For deterministic programs, an equivalent formulation is as follows:

    If `P` holds before `S` is executed, there exists a state in which execution
    terminates normally and `Q` holds in that state.

Example:

    `[i ≤ 100] while i ≠ 100 do i := i + 1 [i = 100]`

In our WHILE language, this only affects while loops, which must now be
annotated by a __variant__ `V` (a natural number that decreases with each
iteration):

    [I ∧ b ∧ V = v₀] S [I ∧ V < v₀]
    ——————————————————————————————— While-Var
    [I] while b do S [I ∧ ¬b]

What is a suitable variant for the example above? -/

end LoVe
