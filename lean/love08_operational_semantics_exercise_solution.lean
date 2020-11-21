import .love08_operational_semantics_demo


/- # LoVe Exercise 8: Operational Semantics -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ≈ S₂`. -/

def big_step_equiv (S₁ S₂ : stmt) : Prop :=
∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix ` ≈ ` := big_step_equiv

/- Program equivalence is a equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

@[refl] lemma big_step_equiv.refl {S : stmt} :
  S ≈ S :=
fix s t,
show (S, s) ⟹ t ↔ (S, s) ⟹ t, from
  by refl

@[symm] lemma big_step_equiv.symm {S₁ S₂ : stmt}:
  S₁ ≈ S₂ → S₂ ≈ S₁ :=
assume h : S₁ ≈ S₂,
fix s t,
show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t, from
  iff.symm (h s t)

@[trans] lemma big_step_equiv.trans {S₁ S₂ S₃ : stmt} (h₁₂ : S₁ ≈ S₂)
    (h₂₃ : S₂ ≈ S₃) :
  S₁ ≈ S₃ :=
fix s t,
show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t, from
  iff.trans (h₁₂ s t) (h₂₃ s t)


/- 1.1. Prove the following program equivalences. -/

lemma big_step_equiv.skip_assign_id {x} :
  stmt.assign x (λs, s x) ≈ stmt.skip :=
begin
  intros s t,
  apply iff.intro,
  { intro hasn,
    cases' hasn,
    simp * at * },
  { intro hskip,
    cases' hskip,
    simp * at * }
end

lemma big_step_equiv.seq_skip_left {S : stmt} :
  stmt.skip ;; S ≈ S :=
begin
  intros s t,
  apply iff.intro,
  { intro h,
    cases' h,
    cases' h_1,
    assumption },
  { intro h,
    exact big_step.seq big_step.skip h }
end

lemma big_step_equiv.seq_skip_right {S : stmt} :
  S ;; stmt.skip ≈ S :=
begin
  intros s t,
  apply iff.intro,
  { intro h,
    cases' h,
    cases' h_1,
    assumption },
  { intro h,
    exact big_step.seq h big_step.skip }
end

lemma big_step_equiv.ite_seq_while {b} {S : stmt} :
  stmt.ite b (S ;; stmt.while b S) stmt.skip ≈ stmt.while b S :=
begin
  intros s t,
  apply iff.intro,
  { intro hite,
    cases' hite,
    { cases' hite,
      apply big_step.while_true; assumption },
    { cases' hite,
      apply big_step.while_false,
      assumption } },
  { intro while,
    cases' while,
    { apply big_step.ite_true hcond,
      apply big_step.seq; assumption },
    { apply big_step.ite_false hcond,
      exact big_step.skip } }
end

/- 1.2. Program equivalence can be used to replace subprograms by other
subprograms with the same semantics. Prove the following so-called congruence
rules: -/

lemma big_step_equiv.seq_congr {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  S₁ ;; T₁ ≈ S₂ ;; T₂ :=
begin
  intros s t,
  apply iff.intro,
  { intro hseq,
    cases' hseq with _ _ _ _ _ _ _ u _ hS₁ hT₁,
    apply big_step.seq,
    { apply iff.elim_left (hS _ _) hS₁ },
    { apply iff.elim_left (hT _ _) hT₁ } },
  { intros hseq,
    cases' hseq with _ _ _ _ _ _ _ u _ hS₂ hT₂,
    apply big_step.seq,
    { exact iff.elim_right (hS _ _) hS₂ },
    { exact iff.elim_right (hT _ _) hT₂ } }
end

lemma big_step_equiv.ite_congr {b} {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  stmt.ite b S₁ T₁ ≈ stmt.ite b S₂ T₂ :=
begin
  intros s t,
  apply iff.intro,
  { intro hite,
    cases' hite,
    case ite_true : _ _ _ _ _ hcond hbody {
      apply big_step.ite_true hcond,
      exact iff.elim_left (hS _ _) hbody },
    case ite_false : _ _ _ _ _ hcond hbody {
      apply big_step.ite_false hcond,
      exact iff.elim_left (hT _ _) hbody } },
  { intro hite,
    cases' hite,
    case ite_true : _ _ _ _ _ hcond hbody {
      apply big_step.ite_true hcond,
      exact iff.elim_right (hS _ _) hbody },
    case ite_false : _ _ _ _ _ hcond hbody {
      apply big_step.ite_false hcond,
      exact iff.elim_right (hT _ _) hbody } }
end

/- 1.3 (**optional**): Prove one more congruence rule. This one is more
difficult. -/

lemma denote_equiv.while_congr {b} {S₁ S₂ : stmt} (hS : S₁ ≈ S₂) :
  stmt.while b S₁ ≈ stmt.while b S₂ :=
begin
  intros s t,
  apply iff.intro,
  { intro hwhile,
    induction' hwhile,
    case while_true : b S t u v hcond hbody hrest ih_body ih_rest {
      apply big_step.while_true hcond,
      exact iff.elim_left (hS _ _) hbody,
      exact ih_rest hS },
    case while_false {
      exact big_step.while_false hcond } },
  { intro hwhile,
    induction' hwhile,
    case while_true : b S t u v hcond hbody hrest ih_body ih_rest {
      apply big_step.while_true hcond,
      exact iff.elim_right (hS _ _) hbody,
      exact ih_rest hS },
    case while_false {
      exact big_step.while_false hcond } }
end


/- ## Question 2: Guarded Command Language (GCL)

In 1976, E. W. Dijkstra introduced the guarded command language, a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert b     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert b` aborts if `b` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace gcl

inductive stmt (σ : Type) : Type
| assign : string → (σ → ℕ) → stmt
| assert : (σ → Prop) → stmt
| seq    : stmt → stmt → stmt
| choice : list stmt → stmt
| loop   : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/- The parameter `σ` abstracts over the state type. It is necessary as a work
around for a Lean bug.

The big-step semantics is defined as follows: -/

inductive big_step : (stmt state × state) → state → Prop
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| assert {b : state → Prop} {s} (hcond : b s) :
  big_step (stmt.assert b, s) s
| seq {S T s t u} (h₁ : big_step (S, s) t) (h₂ : big_step (T, t) u) :
  big_step (S ;; T, s) u
| choice {Ss s t} (i) (hless : i < list.length Ss)
    (hbody : big_step (list.nth_le Ss i hless, s) t) :
  big_step (stmt.choice Ss, s) t
| loop_base {S s} :
  big_step (stmt.loop S, s) s
| loop_step {S s u} (t) (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.loop S, t) u) :
  big_step (stmt.loop S, s) u

infix ` ⟹ ` : 110 := big_step

/- 2.1. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] lemma big_step_assign_iff {x a s t} :
  (stmt.assign x a, s) ⟹ t ↔ t = s{x ↦ a s} :=
begin
  apply iff.intro,
  { intro hasn,
    cases' hasn,
    refl },
  { intro heq,
    rw heq,
    exact big_step.assign }
end

@[simp] lemma big_step_assert {b s t} :
  (stmt.assert b, s) ⟹ t ↔ t = s ∧ b s :=
begin
  apply iff.intro,
  { intro hast,
    cases' hast,
    simp * at * },
  { intros hand,
    cases' hand,
    rw left,
    apply big_step.assert right }
end

@[simp] lemma big_step_seq_iff {S₁ S₂ s t} :
  (stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
begin
  apply iff.intro,
  { intro hseq,
    cases' hseq,
    apply exists.intro,
    apply and.intro; assumption },
  { intro hseq,
    cases' hseq,
    cases' h,
    apply big_step.seq; assumption }
end

lemma big_step_loop {S s u} :
  (stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (stmt.loop S, t) ⟹ u)) :=
begin
  apply iff.intro,
  { intro hloop,
    cases' hloop,
    { apply or.intro_left,
      refl },
    { apply or.intro_right,
      apply exists.intro t,
      cc } },
  { intro hor,
    cases' hor,
    { rw h,
      apply big_step.loop_base },
    { cases' h,
      cases' h,
      apply big_step.loop_step; assumption } }
end

@[simp] lemma big_step_choice {Ss s t} :
  (stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < list.length Ss),
     (list.nth_le Ss i hless, s) ⟹ t) :=
begin
  apply iff.intro,
  { intro hchoice,
    cases' hchoice,
    apply exists.intro i,
    apply exists.intro hless,
    assumption },
  { intro hex,
    cases' hex with i hex,
    cases' hex with hless hstep,
    apply big_step.choice; assumption }
end

end gcl

/- 2.2. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : stmt → gcl.stmt state
| stmt.skip         := gcl.stmt.assert (λ_, true)
| (stmt.assign x a) :=
  gcl.stmt.assign x a
| (S ;; T)          :=
  gcl_of S ;;
  gcl_of T
| (stmt.ite b S T)  :=
  gcl.stmt.choice [
    gcl.stmt.assert b ;; gcl_of S,
    gcl.stmt.assert (λs, ¬ b s) ;; gcl_of T
  ]
| (stmt.while b S)  :=
  gcl.stmt.loop
    (gcl.stmt.assert b ;;
     gcl_of S) ;;
  gcl.stmt.assert (λs, ¬ b s)

/- 2.3. In the definition of `gcl_of` above, `skip` is translated to
`assert (λ_, true)`. Looking at the big-step semantics of both constructs, we
can convince ourselves that it makes sense. Can you think of other correct ways
to define the `skip` case? -/

/- Here are two other possibilities:

* `loop (assert (λ_, false))`
* `assign "x" (λs, s "x")`

There are infinitely many variants, e.g., `seq` of the above two solutions. -/

end LoVe
