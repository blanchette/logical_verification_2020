import .love02_backward_proofs_exercise_sheet


/- # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (6 points + 1 bonus point): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
sorry

lemma em_of_peirce :
  peirce → excluded_middle :=
sorry

lemma dn_of_em :
  excluded_middle → double_negation :=
sorry

end backward_proofs

/- 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
sorry

/- 1.3 (1 bonus point). Supply a structured proof of the following property,
which can be used pull a `∀`-quantifier past an `∃`-quantifier. -/

lemma forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
sorry


/- ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied "Logic and Sets" with Prof. Fokkink, you will know he is
very fond of logic puzzles. This question is meant as a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/- 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

/- 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

end LoVe
