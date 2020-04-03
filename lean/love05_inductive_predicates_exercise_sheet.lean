import .love05_inductive_predicates_demo


/-! # LoVe Exercise 5: Inductive Predicates -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Even and Odd

The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/-! We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/-! 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
sorry

/-! 1.2. Prove that 3, 5, and 7 are odd. -/

-- enter your answer here

/-! 1.3. Complete the following proof by structural induction. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
| 0       := even.zero
| (m + 1) :=
  sorry

/-! 1.4. Complete the following proof by rule induction.

Hint: You can use the `cases` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m :=
begin
  intros n hen,
  induction hen,
  case even.zero {
    apply exists.intro 0,
    refl },
  case even.add_two : k hek ih {
    sorry }
end

/-! 1.6. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
sorry


/-! ## Question 2: Binary Trees

2.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

#check is_full_mirror
#check mirror_mirror

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
sorry

/-! 2.2. Define a `map` function on binary trees, similar to `list.map`. -/

def btree.map {α β : Type} (f : α → β) : btree α → btree β
-- enter the missing cases here

/-! 2.3. Prove the following lemma by case distinction. -/

lemma btree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : btree α, btree.map f t = btree.empty ↔ t = btree.empty :=
sorry

/-! 2.4. Prove the following lemma by rule induction. -/

lemma btree.map_mirror {α β : Type} (f : α → β) :
  ∀t : btree α, is_full t → is_full (btree.map f t) :=
sorry

end LoVe
