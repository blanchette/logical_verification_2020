import .love08_operational_semantics_demo


/-! # LoVe Demo 10: Denotational Semantics

We review a third way to specify the semantics of a programming language:
denotational semantics. Denotational semantics attempt to directly specify the
meaning of programs.

If operational semantics is an idealized interpreter and Hoare logic is an
idealized verifier, then denotational semantics is an idealized compiler.-/


set_option pp.beta true

namespace LoVe


/-! ## Compositionality

A __denotational semantics__ defines the meaning of each program as a
mathematical object:

    `⟦ ⟧ : syntax → semantics`

A key property of denotational semantics is __compositionality__: The meaning of
a compound statement should be defined in terms of the meaning of its
components. This disqualifies

    `⟦S⟧ = {st | (S, prod.fst st) ⟹ prod.snd st}`

i.e.

    `⟦S⟧ = {(s, t) | (S, s) ⟹ t}`

because operational semantics are not compositional.

In short, we want

    `⟦S ; T⟧              = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if b then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while b do S⟧       = … ⟦S⟧ …`

An evaluation function on arithmetic expressions

    `eval : aexp → ((string → ℤ) → ℤ)`

is a denotational semantics. We want the same for imperative programs.


## A Relational Denotational Semantics

We can represent the semantics of an imperative program as a function from
initial state to final state or more generally as a relation between initial
state and final state: `set (state × state)`.

For `skip`, `:=`, `;`, and `if then else`, the denotational semantics is
easy: -/

namespace sorry_defs

def denote : stmt → set (state × state)
| stmt.skip         := Id
| (stmt.assign n a) :=
  {st | prod.snd st = (prod.fst st){n ↦ a (prod.fst st)}}
| (stmt.seq S T)    := denote S ◯ denote T
| (stmt.ite b S T)  := (denote S ⇃ b) ∪ (denote T ⇃ (λs, ¬ b s))
| (stmt.while b S)  := sorry

end sorry_defs

/-! We write `⟦S⟧` for `denote S`. For `while`, we would like to write

    `((denote S ◯ denote (stmt.while b S)) ⇃ b) ∪ (Id ⇃ (λs, ¬ b s))`

but this is ill-founded due to the recursive call on `stmt.while b S`.

What we are looking for is an `X` such that

    `X = ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (λs, ¬ b s))`

In other words, we are looking for a fixpoint.

Most of this lecture is concerned with building a least fixpoint operator
`lfp` that will allow us to define the `while` case as well:

    `lfp (λX, ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (λs, ¬ b s)))`


## Fixpoints

A __fixpoint__ (or fixed point) of `f` is a solution for `X` in the equation

    `X = f X`

In general, fixpoints may not exist at all (e.g., `f := nat.succ`), or there may
be several fixpoints (e.g., `f := id`). But under some conditions on `f`, a
unique __least fixpoint__ and a unique __greatest fixpoint__ are guaranteed to
exist.

Consider this __fixpoint equation__:

    `X = (λ(p : ℕ → Prop) (n : ℕ), n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ p m) X`
      `= (λn : ℕ, n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

where `X : ℕ → Prop` and
`f := (λ(p : ℕ → Prop) (n : ℕ), n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ p m)`.

The above example admits only one fixpoint. The fixpoint equation uniquely
specifies `X` as the set of even numbers.

In general, the least and greatest fixpoint may be different:

    `X = X`

Here, the least fixpoint is `(λ_, False)` and the greatest fixpoint is
`(λ_, True)`. Conventionally, `False < True`, and thus
`(λ_, False) < (λ_, True)`. Similarly, `∅ < @set.univ α` (assuming `α` is
inhabited).

For the semantics of programming languages:

* `X` will have type `set (state × state)` (which is isomorphic to
  `state → state → Prop`), representing relations between states;

* `f` will correspond to either taking one extra iteration of the loop (if the
  condition `b` is true) or the identity (if `b` is false).

Kleene's fixpoint theorem:

    `f^0(∅) ∪ f^1(∅) ∪ f^2(∅) ∪ ⋯ = lfp f`

The least fixpoint corresponds to finite executions of a program, which is all
we care about.

**Key observation**:

    Inductive predicates correspond to least fixpoints, but they are built into
    Lean's logic (the calculus of inductive constructions).


## Monotone Functions

Let `α` and `β` be types with partial order `≤`. A function `f : α → β` is
__monotone__ if

    `a ≤ b → f a ≤ f b`   for all `a`, `b`

Many operations on sets (e.g., `∪`), relations (e.g., `◯`), and functions
(e.g., `λx, x`, `λ_, k`, `∘`) are monotone or preserve monotonicity.

All monotone functions `f : set α → set α` admit least and greatest fixpoints.

**Example of a nonmonotone function**:

    `f A = (if A = ∅ then set.univ else ∅)`

Assuming `α` is inhabited, we have `∅ ⊆ set.univ`, but
`f ∅ = set.univ ⊈ ∅ = f set.univ`. -/

def monotone {α β : Type} [partial_order α] [partial_order β]
  (f : α → β) : Prop :=
∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

lemma monotone_id {α : Type} [partial_order α] :
  monotone (λa : α, a) :=
begin
  intros a₁ a₂ ha,
  exact ha
end

lemma monotone_const {α β : Type} [partial_order α]
    [partial_order β] (b : β) :
  monotone (λ_ : α, b) :=
begin
  intros a₁ a₂ ha,
  exact le_refl b
end

lemma monotone_union {α β : Type} [partial_order α]
    (f g : α → set β) (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ∪ g a) :=
begin
  intros a₁ a₂ ha b hb,
  cases hb,
  { exact or.intro_left _ (hf a₁ a₂ ha hb) },
  { exact or.intro_right _ (hg a₁ a₂ ha hb) }
end

/-! We will prove the following two lemmas in the exercise. -/

namespace sorry_lemmas

lemma monotone_comp {α β : Type} [partial_order α]
    (f g : α → set (β × β)) (hf : monotone f)
    (hg : monotone g) :
  monotone (λa, f a ◯ g a) :=
sorry

lemma monotone_restrict {α β : Type} [partial_order α]
    (f : α → set (β × β)) (p : β → Prop) (hf : monotone f) :
  monotone (λa, f a ⇃ p) :=
sorry

end sorry_lemmas


/-! ## Complete Lattices

To define the least fixpoint on sets, we need `⊆` and `⋂`. Complete lattices
capture this concept abstractly. A __complete lattice__ is an ordered type `α`
for which each set of type `set α` has an infimum.

More precisely, A complete lattice consists of

* a partial order `≤ : α → α → Prop` (i.e., a reflexive, transitive, and
  antisymmetric binary predicate);

* an operator `Inf : set α → α`, called __infimum__.

Moreover, `Inf A` must satisfy these two properties:

* `Inf A` is a lower bound of `A`: `Inf A ≤ b` for all `b ∈ A`;

* `Inf A` is a greatest lower bound: `b ≤ Inf A` for all `b` such that
  `∀a, a ∈ A → b ≤ a`.

**Warning:** `Inf A` is not necessarily an element of `A`.

Examples:

* `set α` is an instance w.r.t. `⊆` and `⋂` for all `α`;
* `Prop` is an instance w.r.t. `→` and `∀` (`Inf A := ∀a ∈ A, a`);
* `enat := ℕ ∪ {∞}`;
* `ereal := ℝ ∪ {- ∞, ∞}`;
* `β → α` if `α` is a complete lattice;
* `α × β` if `α`, `β` are complete lattices.

Finite example (with apologies for the ASCII art):

                Z            Inf {}           = ?
              /   \          Inf {Z}          = ?
             A     B         Inf {A, B}       = ?
              \   /          Inf {Z, A}       = ?
                Y            Inf {Z, A, B, Y} = ?

Nonexamples:

* `ℕ`, `ℤ`, `ℚ`, `ℝ`: no infimum for `∅`, `Inf ℕ`, etc.
* `erat := ℚ ∪ {- ∞, ∞}`: `Inf {q | 2 < q * q} = sqrt 2` is not in `erat`. -/

@[class] structure complete_lattice (α : Type)
  extends partial_order α : Type :=
(Inf    : set α → α)
(Inf_le : ∀A b, b ∈ A → Inf A ≤ b)
(le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A)

/-! For sets: -/

@[instance] def set.complete_lattice {α : Type} :
  complete_lattice (set α) :=
{ le          := (⊆),
  le_refl     := by tautology,
  le_trans    := by tautology,
  le_antisymm :=
    begin
      intros A B hAB hBA,
      apply set.ext,
      tautology
    end,
  Inf         := λ𝒜, {a | ∀A, A ∈ 𝒜 → a ∈ A},
  Inf_le      := by tautology,
  le_Inf      := by tautology }


/-! ## Least Fixpoint -/

def lfp {α : Type} [complete_lattice α] (f : α → α) : α :=
complete_lattice.Inf ({a | f a ≤ a})

lemma lfp_le {α : Type} [complete_lattice α] (f : α → α)
    (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
complete_lattice.Inf_le _ _ h

lemma le_lfp {α : Type} [complete_lattice α] (f : α → α)
    (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f :=
complete_lattice.le_Inf _ _ h

/-! **Knaster-Tarski theorem:** For any monotone function `f`:

* `lfp f` is a fixpoint: `lfp f = f (lfp f)` (lemma `lfp_eq`);
* `lfp f` is smaller than any other fixpoint: `X = f X → lfp f ≤ X`. -/

lemma lfp_eq {α : Type} [complete_lattice α] (f : α → α)
    (hf : monotone f) :
  lfp f = f (lfp f) :=
begin
  have h : f (lfp f) ≤ lfp f :=
    begin
      apply le_lfp,
      intros a' ha',
      apply @le_trans _ _ _ (f a'),
      { apply hf,
        apply lfp_le,
        assumption },
      { assumption }
    end,
  apply le_antisymm,
  { apply lfp_le,
    apply hf,
    assumption },
  { assumption }
end


/-! ## A Relational Denotational Semantics, Continued -/

def denote : stmt → set (state × state)
| stmt.skip         := Id
| (stmt.assign x a) :=
  {st | prod.snd st = (prod.fst st){x ↦ a (prod.fst st)}}
| (stmt.seq S T)    := denote S ◯ denote T
| (stmt.ite b S T)  := (denote S ⇃ b) ∪ (denote T ⇃ (λs, ¬ b s))
| (stmt.while b S)  :=
  lfp (λX, ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (λs, ¬ b s)))

notation `⟦` S `⟧`:= denote S


/-! ## Application to Program Equivalence

Based on the denotational semantics, we introduce the notion of program
equivalence: `S₁ ~ S₂`. (Compare with exercise 8.) -/

def denote_equiv (S₁ S₂ : stmt) : Prop :=
⟦S₁⟧ = ⟦S₂⟧

infix ` ~ ` := denote_equiv

/-! It is obvious from the definition that `~` is an equivalence relation.

Program equivalence can be used to replace subprograms by other subprograms with
the same semantics. This is achieved by the following congruence rules: -/

lemma denote_equiv.seq_congr {S₁ S₂ T₁ T₂ : stmt}
    (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  S₁ ;; T₁ ~ S₂ ;; T₂ :=
by simp [denote_equiv, denote, *] at *

lemma denote_equiv.ite_congr {b} {S₁ S₂ T₁ T₂ : stmt}
    (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  stmt.ite b S₁ T₁ ~ stmt.ite b S₂ T₂ :=
by simp [denote_equiv, denote, *] at *

lemma denote_equiv.while_congr {b} {S₁ S₂ : stmt}
    (hS : S₁ ~ S₂) :
  stmt.while b S₁ ~ stmt.while b S₂ :=
by simp [denote_equiv, denote, *] at *

/-! Compare the simplicity of these proofs with the corresponding proofs for a
big-step semantics (exercise 8).

Let us prove some program equivalences. -/

lemma denote_equiv.skip_assign_id {x} :
  stmt.assign x (λs, s x) ~ stmt.skip :=
by simp [denote_equiv, denote, Id]

lemma denote_equiv.seq_skip_left {S : stmt} :
  stmt.skip ;; S ~ S :=
by simp [denote_equiv, denote, Id, comp]

lemma denote_equiv.seq_skip_right {S : stmt} :
  S ;; stmt.skip ~ S :=
by simp [denote_equiv, denote, Id, comp]

lemma denote_equiv.ite_seq_while {b} {S : stmt} :
  stmt.ite b (S ;; stmt.while b S) stmt.skip ~ stmt.while b S :=
begin
  simp [denote_equiv, denote],
  apply eq.symm,
  apply lfp_eq,
  apply monotone_union,
  { apply sorry_lemmas.monotone_restrict,
    apply sorry_lemmas.monotone_comp,
    { exact monotone_const _ },
    { exact monotone_id } },
  { apply sorry_lemmas.monotone_restrict,
    exact monotone_const _ }
end


/-! ## Equivalence of the Denotational and the Big-Step Semantics
## (**optional**) -/

lemma denote_of_big_step (S : stmt) (s t : state) :
  (S, s) ⟹ t → (s, t) ∈ ⟦S⟧ :=
begin
  generalize hSs : (S, s) = Ss,
  intro h,
  induction h generalizing S s; cases hSs;
    try { solve1 { simp [denote, *] } },
  { apply exists.intro h_t,
    tautology },
  { rewrite eq.symm denote_equiv.ite_seq_while,
    simp [denote, *],
    apply exists.intro h_t,
    apply and.intro,
    { tautology },
    { apply h_ih_hrest (stmt.while h_b h_S),
      refl } },
  { rewrite eq.symm denote_equiv.ite_seq_while,
    simp [denote, *] }
end

lemma big_step_of_denote :
  ∀(S : stmt) (s t : state), (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
| stmt.skip         s t := by simp [denote]
| (stmt.assign n a) s t := by simp [denote]
| (stmt.seq S T)    s t :=
  begin
    intro h,
    cases h with u hu,
    exact big_step.seq
      (big_step_of_denote S _ _ (and.elim_left hu))
      (big_step_of_denote T _ _ (and.elim_right hu))
  end
| (stmt.ite b S T)  s t :=
  begin
    intro h,
    cases h,
    case or.inl {
      cases h,
      apply big_step.ite_true h_left,
      exact big_step_of_denote _ _ _ h_right },
    case or.inr {
      cases h,
      apply big_step.ite_false h_left,
      exact big_step_of_denote _ _ _ h_right }
  end
| (stmt.while b S)  s t :=
  begin
    have hw : ⟦stmt.while b S⟧
        ≤ {st | (stmt.while b S, prod.fst st) ⟹ prod.snd st} :=
      begin
        apply lfp_le _ _ _,
        intros x hx,
        cases x with s t,
        simp at hx,
        cases hx,
        case or.inl {
          cases hx with hs hst,
          cases hst with u hu,
          apply big_step.while_true hs,
          { exact big_step_of_denote S _ _ (and.elim_left hu) },
          { exact and.elim_right hu } },
        case or.inr {
          cases hx,
          cases hx_right,
          apply big_step.while_false hx_left }
      end,
    apply hw
  end

lemma denote_iff_big_step (S : stmt) (s t : state) :
  (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
iff.intro (big_step_of_denote S s t) (denote_of_big_step S s t)

end LoVe
