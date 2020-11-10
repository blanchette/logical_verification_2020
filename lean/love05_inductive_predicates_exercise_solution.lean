import .love05_inductive_predicates_demo


/- # LoVe Exercise 5: Inductive Predicates -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Even and Odd

The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/- We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases'` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
begin
  intro h,
  cases' h
end

/- 1.2. Prove that 3, 5, and 7 are odd. -/

lemma odd_3 :
  odd 3 :=
begin
  intro h,
  cases' h,
  cases' h
end

lemma odd_5 :
  odd 5 :=
begin
  intro h,
  cases' h,
  cases' h,
  cases' h
end

lemma odd_7 :
  odd 7 :=
begin
  intro h,
  cases' h,
  cases' h,
  cases' h,
  cases' h
end

/- 1.3. Complete the following proof by structural induction. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
| 0       := even.zero
| (m + 1) :=
  begin
    apply even.add_two,
    simp,
    apply even_two_times
  end

/- 1.4. Complete the following proof by rule induction.

Hint: You can use the `cases'` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m :=
begin
  intros n hen,
  induction' hen,
  case zero {
    apply exists.intro 0,
    refl },
  case add_two : k hek ih {
    cases' ih with w hk,
    apply exists.intro (w + 1),
    rw hk,
    linarith }
end

/- 1.6. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
begin
  apply iff.intro,
  { apply even_imp_exists_two_times },
  { intro h,
    cases' h,
    simp *,
    apply even_two_times }
end


/- ## Question 2: Binary Trees

2.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

#check is_full_mirror
#check mirror_mirror

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
begin
  intros t fmt,
  have fmmt : is_full (mirror (mirror t)) :=
    is_full_mirror _ fmt,
  rw mirror_mirror at fmmt,
  assumption
end

/- 2.2. Define a `map` function on binary trees, similar to `list.map`. -/

def btree.map {α β : Type} (f : α → β) : btree α → btree β
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node (f a) (btree.map l) (btree.map r)

/- 2.3. Prove the following lemma by case distinction. -/

lemma btree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : btree α, btree.map f t = btree.empty ↔ t = btree.empty
| btree.empty        := by simp [btree.map]
| (btree.node _ _ _) := by simp [btree.map]

/- 2.4. Prove the following lemma by rule induction. -/

lemma btree.map_mirror {α β : Type} (f : α → β) :
  ∀t : btree α, is_full t → is_full (btree.map f t) :=
begin
  intros t hfull,
  induction' hfull,
  case empty {
    simp [btree.map],
    exact is_full.empty },
  case node {
    simp [btree.map],
    apply is_full.node,
    { exact ih_hfull f },
    { exact ih_hfull_1 f },
    { simp [btree.map_eq_empty_iff],
      assumption } }
end

end LoVe
