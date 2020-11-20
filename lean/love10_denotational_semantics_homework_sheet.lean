import .love10_denotational_semantics_demo


/- # LoVe Homework 10: Denotational Semantics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (7 points): Denotational Semantics of DOWHILE -/

namespace do_while

/- Consider the following DOWHILE language: -/

inductive stmt : Type
| skip     : stmt
| assign   : string → (state → ℕ) → stmt
| seq      : stmt → stmt → stmt
| unless   : stmt → (state → Prop) → stmt
| while    : (state → Prop) → stmt → stmt
| do_while : stmt → (state → Prop) → stmt

infixr ` ;; ` : 90 := stmt.seq

/- The `skip`, `assign`, `seq`, and `while constructs are as for the WHILE
language.

`unless S b` executes `S` if `b` is false in the current state; otherwise, it
does nothing. This statement is inspired by Perl's `unless` conditional.

`do_while S b` first executes `S`. Then, if `b` is true in the resulting state,
it re-enters the loop and executes `S` again, and continues executing `S` until
`b` becomes `false`. The semantics is almost the same as `while b S`, except
that `p` is always executed at least once, even if the condition is not true
initially. This statement is inspired by C's and Java's `do { … } while (…)`
loop.

1.1 (2 points). Give a denotational semantics of DOWHILE.

Hint: Your definition should make it easy to prove lemma `do_while_while` in
question 1.2. -/

def denote : stmt → set (state × state)
| stmt.skip           := Id
-- enter the missing cases here

notation `⟦` S `⟧`:= denote S

/- 1.2 (1 point). Prove the following correspondence between `do_while` and
`while`. -/

lemma do_while_while (S : stmt) (b : state → Prop) :
  ⟦stmt.do_while S b⟧ = ⟦S⟧ ◯ ⟦stmt.while b S⟧ :=
sorry

/- 1.3 (4 points). Prove the following lemmas.

Hint: For all of these, short proofs are possible. -/

lemma lfp_const {α : Type} [complete_lattice α] (a : α) :
  lfp (λX, a) = a :=
sorry

lemma while_false (S : stmt) :
  ⟦stmt.while (λ_, false) S⟧ = Id :=
sorry

lemma comp_Id {α : Type} (r : set (α × α)) :
  r ◯ Id = r :=
sorry

lemma do_while_false (S : stmt) :
  ⟦stmt.do_while S (λ_, false)⟧ = ⟦S⟧ :=
sorry

end do_while


/- ## Question 2 (2 points + 2 bonus points): Kleene's Theorem

We can compute the fixpoint by iteration by taking the union of all finite
iterations of `f`:

    `lfp f = ⋃i, (f ^^ i) ∅`

where

    `f ^^ i = f ∘ ⋯ ∘ f`

iterates the function `f` `i` times. However, the above characterization of
`lfp` only holds for continuous functions, a concept we will introduce below. -/

def iterate {α : Type} (f : α → α) : ℕ → α → α
| 0       a := a
| (n + 1) a := f (iterate n a)

notation f`^^`n := iterate f n

/- 2.1 (2 points). Fill in the missing proofs below. -/

def Union {α : Type} (s : ℕ → set α) : set α :=
{a | ∃n, a ∈ s n}

lemma Union_le {α : Type} {s : ℕ → set α} (A : set α) (h : ∀i, s i ≤ A) :
  Union s ≤ A :=
sorry

/- A continuous function `f` is a function that commutes with the union of any
monotone sequence `s`: -/

def continuous {α : Type} (f : set α → set α) : Prop :=
∀s : ℕ → set α, monotone s → f (Union s) = Union (λi, f (s i))

/- We need to prove that each continuous function is monotone. To achieve this,
we will need the following sequence: -/

def bi_seq {α : Type} (A B : set α) : ℕ → set α
| 0       := A
| (n + 1) := B

/- For example, `bi_seq A B` is the sequence A, B, B, B, …. -/

lemma monotone_bi_seq {α : Type} (A B : set α) (h : A ≤ B) :
  monotone (bi_seq A B)
| 0       0       _ := le_refl _
| 0       (n + 1) _ := h
| (n + 1) (m + 1) _ := le_refl _

lemma Union_bi_seq {α : Type} (A B : set α) (ha : A ≤ B) :
  Union (bi_seq A B) = B :=
begin
  apply le_antisymm,
  { sorry },
  { sorry }
end

lemma monotone_of_continuous {α : Type} (f : set α → set α)
    (hf : continuous f) :
  monotone f :=
sorry

/- 2.2 (1 bonus point). Provide the following proof, using a similar case
distinction as for `monotone_bi_seq` above. -/

lemma monotone_iterate {α : Type} (f : set α → set α) (hf : monotone f) :
  monotone (λi, (f ^^ i) ∅) :=
sorry

/- 2.3 (1 bonus point). Prove the main theorem. A proof sketch is given below.

We break the proof into two proofs of inclusion.

Case 1. `lfp f ≤ Union (λi, (f ^^ i) ∅)`: The key is to use the lemma `lfp_le`
together with continuity of `f`.

Case 2. `Union (λi, (f ^^ i) ∅) ≤ lfp f`: The lemma `Union_le` gives us a
natural number `i`, on which you can perform induction. We also need the lemma
`lfp_eq` to unfold one iteration of `lfp f`. -/

lemma lfp_Kleene {α : Type} (f : set α → set α) (hf : continuous f) :
  lfp f = Union (λi, (f ^^ i) ∅) :=
sorry

end LoVe
