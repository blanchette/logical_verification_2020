import .lovelib


/- # LoVe Demo 8: Operational Semantics

In this and the next two lectures, we will see how to use Lean to specify the
syntax and semantics of programming languages and to reason about the
semantics. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Formal Semantics

A formal semantics helps specify and reason about the programming language
itself, and about individual programs.

It can form the basis of verified compilers, interpreters, verifiers, static
analyzers, type checkers, etc. Without formal proofs, these tools are
**almost always wrong**.

In this area, proof assistants are widely used. Every year, about 10-20% of POPL
papers are partially or totally formalized. Reasons for this success:

* Little machinery (background libraries, tactics) is needed to get started,
  beyond inductive types and predicates and recursive functions.

* The proofs tend to have lots of cases, which is a good match for computers.

* Proof assistants keep track of what needs to be changed when as extend the
  programming language with more features.

Case in point: WebAssembly. To quote Conrad Watt (with some abbreviations):

    We have produced a full Isabelle mechanisation of the core execution
    semantics and type system of the WebAssembly language. To complete this
    proof, **several deficiencies** in the official WebAssembly specification,
    uncovered by our proof and modelling work, needed to be corrected. In some
    cases, these meant that the type system was **originally unsound**.

    We have maintained a constructive dialogue with the working group,
    verifying new features as they are added. In particular, the mechanism by
    which a WebAssembly implementation interfaces with its host environment was
    not formally specified in the working group's original paper. Extending our
    mechanisation to model this feature revealed a deficiency in the WebAssembly
    specification that **sabotaged the soundness** of the type system.


## A Minimalistic Imperative Language

__WHILE__ is a minimalistic imperative language with the following grammar:

    S  ::=  skip                 -- no-op
         |  x := a               -- assignment
         |  S ; S                -- sequential composition
         |  if b then S else S   -- conditional statement
         |  while b do S         -- while loop

where `S` stands for a statement (also called command or program), `x` for a
variable, `a` for an arithmetic expression, and `b` for a Boolean expression. -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| ite    : (state → Prop) → stmt → stmt → stmt
| while  : (state → Prop) → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/- In our grammar, we deliberately leave the syntax of arithmetic and Boolean
expressions unspecified. In Lean, we have the choice:

* We could use a type such as `aexp` from lecture 1 and similarly for Boolean
  expressions.

* Supposing a state `s` is a function from variable names to values
  (`string → ℕ`), we could decide that an arithmetic expression is simply a
  function from states to natural numbers (`state → ℕ`) and a Boolean expression
  is a predicate (`state → Prop` or `state → bool`).

This corresponds to the difference between deep and shallow embeddings:

* A __deep embedding__ of some syntax (expression, formula, program, etc.)
  consists of an abstract syntax tree specified in the proof assistant
  (e.g., `aexp`) with a semantics (e.g., `eval`).

* In contrast, a __shallow embedding__ simply reuses the corresponding
  mechanisms from the logic (e.g., λ-terms, functions and predicate types).

A deep embedding allows us to reason about the syntax (and its semantics). A
shallow embedding is more lightweight, because we can use it directly, without
having to define a semantics.

We will use a deep embedding of programs (which we find interesting), and
shallow embeddings of assignments and Boolean expressions (which we find
boring).

Examples:

    `λs : state, s "x" + s "y" + 1`   -- x + y + 1
    `λs : state, s "a" ≠ s "b"`       -- a ≠ b


## Big-Step Semantics

An __operational semantics__ corresponds to an idealized interpreter (specified
in a Prolog-like language). Two main variants:

* big-step semantics;

* small-step semantics.

In a __big-step semantics__ (also called __natural semantics__), judgments have
the form `(S, s) ⟹ t`:

    Starting in a state `s`, executing `S` terminates in the state `t`.

Example:

    `(x := x + y; y := 0, [x ↦ 3, y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]`

Derivation rules:

    ——————————————— Skip
    (skip, s) ⟹ s

    ——————————————————————————— Asn
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ s'   (S', s') ⟹ s''
    ——————————————————————————————— Seq
    (S; S', s) ⟹ s''

    (S, s) ⟹ s'
    ——————————————————————————————— If-True   if s(b) is true
    (if b then S else S', s) ⟹ s'

    (S', s) ⟹ s'
    ——————————————————————————————— If-False   if s(b) is false
    (if b then S else S', s) ⟹ s'

    (S, s) ⟹ s'   (while b do S, s') ⟹ s''
    —————————————————————————————————————————— While-True   if s(b) is true
    (while b do S, s) ⟹ s''

    ————————————————————————— While-False   if s(b) is false
    (while b do S, s) ⟹ s

Above, `s(e)` denotes the value of expression `e` in state `s`.

In Lean, the judgment corresponds to an inductive predicate, and the derivation
rules correspond to the predicate's introduction rules. Using an inductive
predicate as opposed to a recursive function allows us to cope with
nontermination (e.g., a diverging `while`) and nondeterminism (e.g.,
multithreading). -/

inductive big_step : stmt × state → state → Prop
| skip {s} :
  big_step (stmt.skip, s) s
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
| ite_true {b : state → Prop} {S T s t} (hcond : b s)
    (hbody : big_step (S, s) t) :
  big_step (stmt.ite b S T, s) t
| ite_false {b : state → Prop} {S T s t} (hcond : ¬ b s)
    (hbody : big_step (T, s) t) :
  big_step (stmt.ite b S T, s) t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.while b S, t) u) :
  big_step (stmt.while b S, s) u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  big_step (stmt.while b S, s) s

infix ` ⟹ ` : 110 := big_step


/- ## Properties of the Big-Step Semantics

Equipped with a big-step semantics, we can

* prove properties of the programming language, such as **equivalence proofs**
  between programs and **determinism**;

* reason about **concrete programs**, proving theorems relating final states `t`
  with initial states `s`. -/

lemma big_step_deterministic {S s l r} (hl : (S, s) ⟹ l)
    (hr : (S, s) ⟹ r) :
  l = r :=
begin
  induction' hl,
  case skip : t {
    cases' hr,
    refl },
  case assign : x a s {
    cases' hr,
    refl },
  case seq : S T s t l hS hT ihS ihT {
    cases' hr with _ _ _ _ _ _ _ t' _ hS' hT',
    cases' ihS hS',
    cases' ihT hT',
    refl },
  case ite_true : b S T s t hb hS ih {
    cases' hr,
    { apply ih,
      assumption },
    { apply ih,
      cc } },
  case ite_false : b S T s t hb hT ih {
    cases' hr,
    { apply ih,
      cc },
    { apply ih,
      assumption } },
  case while_true : b S s t u hb hS hw ihS ihw {
    cases' hr,
    { cases' ihS hr,
      cases' ihw hr_1,
      refl },
    { cc } },
  { cases' hr,
    { cc },
    { refl } }
end

lemma big_step_terminates {S s} :
  ∃t, (S, s) ⟹ t :=
sorry   -- unprovable

lemma big_step_doesnt_terminate {S s t} :
  ¬ (stmt.while (λ_, true) S, s) ⟹ t :=
begin
  intro hw,
  induction' hw,
  case while_true {
    assumption },
  case while_false {
    cc }
end

@[simp] lemma big_step_skip_iff {s t} :
  (stmt.skip, s) ⟹ t ↔ t = s :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    refl },
  { intro h,
    rw h,
    exact big_step.skip }
end

@[simp] lemma big_step_assign_iff {x a s t} :
  (stmt.assign x a, s) ⟹ t ↔ t = s{x ↦ a s} :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    refl },
  { intro h,
    rw h,
    exact big_step.assign }
end

@[simp] lemma big_step_seq_iff {S T s t} :
  (S ;; T, s) ⟹ t ↔ (∃u, (S, s) ⟹ u ∧ (T, u) ⟹ t) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    apply exists.intro,
    apply and.intro; assumption },
  { intro h,
    cases' h,
    cases' h,
    apply big_step.seq; assumption }
end

@[simp] lemma big_step_ite_iff {b S T s t} :
  (stmt.ite b S T, s) ⟹ t ↔
  (b s ∧ (S, s) ⟹ t) ∨ (¬ b s ∧ (T, s) ⟹ t) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { apply or.intro_left,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases' h; cases' h,
    { apply big_step.ite_true; assumption },
    { apply big_step.ite_false; assumption } }
end

lemma big_step_while_iff {b S s u} :
  (stmt.while b S, s) ⟹ u ↔
  (∃t, b s ∧ (S, s) ⟹ t ∧ (stmt.while b S, t) ⟹ u)
  ∨ (¬ b s ∧ u = s) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { apply or.intro_left,
      apply exists.intro t,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases' h,
    case inl {
      cases' h with t h,
      cases' h with hb h,
      cases' h with hS hwhile,
      exact big_step.while_true hb hS hwhile },
    case inr {
      cases' h with hb hus,
      rw hus,
      exact big_step.while_false hb } }
end

lemma big_step_while_true_iff {b : state → Prop} {S s u}
    (hcond : b s) :
  (stmt.while b S, s) ⟹ u ↔
  (∃t, (S, s) ⟹ t ∧ (stmt.while b S, t) ⟹ u) :=
by rw big_step_while_iff; simp [hcond]

@[simp] lemma big_step_while_false_iff {b : state → Prop}
    {S s t} (hcond : ¬ b s) :
  (stmt.while b S, s) ⟹ t ↔ t = s :=
by rw big_step_while_iff; simp [hcond]


/- ## Small-Step Semantics

A big-step semantics

* does not let us reason about intermediate states;

* does not let us express nontermination or interleaving (for multithreading).

__Small-step semantics__ (also called __structural operational semantics__)
solve the above issues.

A judgment has the form `(S, s) ⇒ (T, t)`:

    Starting in a state `s`, executing one step of `S` leaves us in the
    state `t`, with the program `T` remaining to be executed.

An execution is a finite or infinite chain `(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`.

A pair `(S, s)` is called a __configuration__. It is __final__ if no transition
of the form `(S, s) ⇒ _` is possible.

Example:

      `(x := x + y; y := 0, [x ↦ 3, y ↦ 5])`
    `⇒ (skip; y := 0,       [x ↦ 8, y ↦ 5])`
    `⇒ (y := 0,             [x ↦ 8, y ↦ 5])`
    `⇒ (skip,               [x ↦ 8, y ↦ 0])`

Derivation rules:

    ————————————————————————————————— Asn
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ———————————————————————— Seq-Step
    (S; T, s) ⇒ (S' ; T, s')

    —————————————————————— Seq-Skip
    (skip ; S, s) ⇒ (S, s)

    ————————————————————————————————— If-True   if s(b) is true
    (if b then S else S', s) ⇒ (S, s)

    —————————————————————————————————— If-False   if s(b) is false
    (if b then S else S', s) ⇒ (S', s)

    ————————————————————————————————————————————————————————————————— While
    (while b do S, s) ⇒ (if b then (S ; while b do S) else skip, s)

There is no rule for `skip` (why?). -/

inductive small_step : stmt × state → stmt × state → Prop
| assign {x a s} :
  small_step (stmt.assign x a, s) (stmt.skip, s{x ↦ a s})
| seq_step {S S' T s s'} (hS : small_step (S, s) (S', s')) :
  small_step (S ;; T, s) (S' ;; T, s')
| seq_skip {T s} :
  small_step (stmt.skip ;; T, s) (T, s)
| ite_true {b : state → Prop} {S T s} (hcond : b s) :
  small_step (stmt.ite b S T, s) (S, s)
| ite_false {b : state → Prop} {S T s} (hcond : ¬ b s) :
  small_step (stmt.ite b S T, s) (T, s)
| while {b : state → Prop} {S s} :
  small_step (stmt.while b S, s)
    (stmt.ite b (S ;; stmt.while b S) stmt.skip, s)

infixr ` ⇒ ` := small_step
infixr ` ⇒* ` : 100 := star small_step


/- Equipped with a small-step semantics, we can **define** a big-step
semantics:

> `(S, s) ⟹ s'` if and only if `(S, s) ⇒* (skip, s')`

where `r*` denotes the reflexive transitive closure of a relation `r`.

Alternatively, if we have already defined a big-step semantics, we can **prove**
the above equivalence theorem to validate our definitions.

The main disadvantage of small-step semantics is that we now have two relations,
`⇒` and `⇒*`, and reasoning tends to be more complicated.


## Properties of the Small-Step Semantics

We can prove that a configuration `(S, s)` is final if and only if `S = skip`.
This ensures that we have not forgotten a derivation rule. -/

lemma small_step_final (S s) :
  (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = stmt.skip :=
begin
  induction' S,
  case skip {
    simp,
    intros T t hstep,
    cases' hstep },
  case assign : x a {
    simp,
    apply exists.intro stmt.skip,
    apply exists.intro (s{x ↦ a s}),
    exact small_step.assign },
  case seq : S T ihS ihT {
    simp,
    cases' classical.em (S = stmt.skip),
    case inl {
      rw h,
      apply exists.intro T,
      apply exists.intro s,
      exact small_step.seq_skip },
    case inr {
      simp [h, auto.not_forall_eq, auto.not_not_eq] at ihS,
      cases' ihS s with S' hS',
      cases' hS' with s' hs',
      apply exists.intro (S' ;; T),
      apply exists.intro s',
      exact small_step.seq_step hs' } },
  case ite : b S T ihS ihT {
    simp,
    cases' classical.em (b s),
    case inl {
      apply exists.intro S,
      apply exists.intro s,
      exact small_step.ite_true h },
    case inr {
      apply exists.intro T,
      apply exists.intro s,
      exact small_step.ite_false h } },
  case while : b S ih {
    simp,
    apply exists.intro (stmt.ite b (S ;; stmt.while b S) stmt.skip),
    apply exists.intro s,
    exact small_step.while }
end

lemma small_step_deterministic {S s Ll Rr}
    (hl : (S, s) ⇒ Ll) (hr : (S, s) ⇒ Rr) :
  Ll = Rr :=
begin
  induction' hl,
  case assign : x a s {
    cases' hr,
    refl },
  case seq_step : S S₁ T s s₁ hS₁ ih {
    cases' hr,
    case seq_step : S S₂ _ _ s₂ hS₂ {
      have hSs₁₂ := ih hS₂,
      cc },
    case seq_skip {
      cases' hS₁ } },
  case seq_skip : T s {
    cases' hr,
    { cases' hr },
    { refl } },
  case ite_true : b S T s hcond {
    cases' hr,
    case ite_true {
      refl },
    case ite_false {
      cc } },
  case ite_false : b S T s hcond {
    cases' hr,
    case ite_true {
      cc },
    case ite_false {
      refl } },
  case while : b S s {
    cases' hr,
    refl }
end

/- We can define inversion rules also about the small-step semantics. Here are
three examples: -/

lemma small_step_skip {S s t} :
  ¬ ((stmt.skip, s) ⇒ (S, t)) :=
by intro h; cases' h

@[simp] lemma small_step_seq_iff {S T s Ut} :
  (S ;; T, s) ⇒ Ut ↔
  (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S' ;; T, t))
  ∨ (S = stmt.skip ∧ Ut = (T, s)) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { apply or.intro_left,
      apply exists.intro S',
      apply exists.intro s',
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases' h,
    { cases' h,
      cases' h,
      cases' h,
      rw right,
      apply small_step.seq_step,
      assumption },
    { cases' h,
      rw left,
      rw right,
      apply small_step.seq_skip } }
end

@[simp] lemma small_step_ite_iff {b S T s Us} :
  (stmt.ite b S T, s) ⇒ Us ↔
  (b s ∧ Us = (S, s)) ∨ (¬ b s ∧ Us = (T, s)) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { apply or.intro_left,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases' h,
    { cases' h,
      rw right,
      apply small_step.ite_true,
      assumption },
    { cases' h,
      rw right,
      apply small_step.ite_false,
      assumption } }
end


/- ### Equivalence of the Big-Step and the Small-Step Semantics (**optional**)

A more important result is the connection between the big-step and the
small-step semantics:

    `(S, s) ⟹ t ↔ (S, s) ⇒* (stmt.skip, t)`

Its proof, given below, is beyond the scope of this course. -/

lemma star_small_step_seq {S T s u}
    (h : (S, s) ⇒* (stmt.skip, u)) :
  (S ;; T, s) ⇒* (stmt.skip ;; T, u) :=
begin
  apply star.lift (λSs, (prod.fst Ss ;; T, prod.snd Ss)) _ h,
  intros Ss Ss' h,
  cases' Ss,
  cases' Ss',
  apply small_step.seq_step,
  assumption
end

lemma star_small_step_of_big_step {S s t} (h : (S, s) ⟹ t) :
  (S, s) ⇒* (stmt.skip, t) :=
begin
  induction' h,
  case skip {
    refl },
  case assign {
    exact star.single small_step.assign },
  case seq : S T s t u hS hT ihS ihT {
    transitivity,
    exact star_small_step_seq ihS,
    apply star.head small_step.seq_skip ihT },
  case ite_true : b S T s t hs hst ih {
    exact star.head (small_step.ite_true hs) ih },
  case ite_false : b S T s t hs hst ih {
    exact star.head (small_step.ite_false hs) ih },
  case while_true : b S s t u hb hS hw ihS ihw {
    exact (star.head small_step.while
      (star.head (small_step.ite_true hb)
         (star.trans (star_small_step_seq ihS)
            (star.head small_step.seq_skip ihw)))) },
  case while_false : b S s hb {
    exact star.tail (star.single small_step.while)
      (small_step.ite_false hb) }
end

lemma big_step_of_small_step_of_big_step {S₀ S₁ s₀ s₁ s₂}
  (h₁ : (S₀, s₀) ⇒ (S₁, s₁)) :
  (S₁, s₁) ⟹ s₂ → (S₀, s₀) ⟹ s₂ :=
begin
  induction' h₁;
    simp [*, big_step_while_true_iff] {contextual := tt},
  case seq_step {
    intros u hS' hT,
    apply exists.intro u,
    exact and.intro (ih hS') hT }
end

lemma big_step_of_star_small_step {S s t} :
  (S, s) ⇒* (stmt.skip, t) → (S, s) ⟹ t :=
begin
  generalize hSs : (S, s) = Ss,
  intro h,
  induction h
      using LoVe.rtc.star.head_induction_on
      with _ S's' h h' ih
      generalizing S s;
    cases' hSs,
  { exact big_step.skip },
  { cases' S's' with S' s',
    apply big_step_of_small_step_of_big_step h,
    apply ih,
    refl }
end

lemma big_step_iff_star_small_step {S s t} :
  (S, s) ⟹ t ↔ (S, s) ⇒* (stmt.skip, t) :=
iff.intro star_small_step_of_big_step
  big_step_of_star_small_step


/- ## Parallelism (**optional**) -/

inductive par_step :
    nat → list stmt × state → list stmt × state → Prop
| intro {Ss Ss' S S' s s' i}
    (hi : i < list.length Ss)
    (hS : S = list.nth_le Ss i hi)
    (hs : (S, s) ⇒ (S', s'))
    (hS' : Ss' = list.update_nth Ss i S') :
  par_step i (Ss, s) (Ss', s')

lemma par_step_diamond {i j Ss Ts Ts' s t t'}
    (hi : i < list.length Ss)
    (hj : j < list.length Ss)
    (hij : i ≠ j)
    (hT : par_step i (Ss, s) (Ts, t))
    (hT' : par_step j (Ss, s) (Ts', t')) :
  ∃u Us, par_step j (Ts, t) (Us, u) ∧
    par_step i (Ts', t') (Us, u) :=
sorry   -- unprovable

def stmt.W : stmt → set string
| stmt.skip         := ∅
| (stmt.assign x _) := {x}
| (stmt.seq S T)    := stmt.W S ∪ stmt.W T
| (stmt.ite _ S T)  := stmt.W S ∪ stmt.W T
| (stmt.while _ S)  := stmt.W S

def exp.R {α : Type} : (state → α) → set string
| f := {x | ∀s n, f (s{x ↦ n}) ≠ f s}

def stmt.R : stmt → set string
| stmt.skip         := ∅
| (stmt.assign _ a) := exp.R a
| (stmt.seq S T)    := stmt.R S ∪ stmt.R T
| (stmt.ite b S T)  := exp.R b ∪ stmt.R S ∪ stmt.R T
| (stmt.while b S)  := exp.R b ∪ stmt.R S

def stmt.V : stmt → set string
| S := stmt.W S ∪ stmt.R S

lemma par_step_diamond_VW_disjoint {i j Ss Ts Ts' s t t'}
    (hiS : i < list.length Ss)
    (hjT : j < list.length Ts)
    (hij : i ≠ j)
    (hT : par_step i (Ss, s) (Ts, t))
    (hT' : par_step j (Ss, s) (Ts', t'))
    (hWV : stmt.W (list.nth_le Ss i hiS)
       ∩ stmt.V (list.nth_le Ts j hjT) = ∅)
    (hVW : stmt.V (list.nth_le Ss i hiS)
       ∩ stmt.W (list.nth_le Ts j hjT) = ∅) :
  ∃u Us, par_step j (Ts, t) (Us, u) ∧
    par_step i (Ts', t') (Us, u) :=
sorry   -- this should be provable

end LoVe
