import .lovelib


/- # LoVe Exercise 3: Forward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha : a,
show a, from
  ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha : a,
assume hb : b,
show b, from
  hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume hg : a → b → c,
assume hb : b,
assume ha : a,
show c, from
  hg ha hb

lemma proj_1st (a : Prop) :
  a → a → a :=
assume ha ha' : a,
show a, from
  ha

/- Please give a different answer than for `proj_1st`. -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
assume ha ha' : a,
show a, from
  ha'

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume hg : a → b → c,
assume ha : a,
assume hf : a → c,
assume hb : b,
have hc : c :=
  hf ha,
show c, from
  hc

/- 1.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume hab : a → b,
assume hnb : ¬ b,
assume ha : a,
have hb : b :=
  hab ha,
show false, from
  hnb hb

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
iff.intro
  (assume hpq : ∀x, p x ∧ q x,
   have hp : ∀x, p x :=
     fix x,
     and.elim_left (hpq x),
   have hq : ∀x, q x :=
     fix x,
     and.elim_right (hpq x),
   show (∀x, p x) ∧ (∀x, q x), from
     and.intro hp hq)
  (assume hpq : (∀x, p x) ∧ (∀x, q x),
   have hp : ∀x, p x :=
     and.elim_left hpq,
   have hq : ∀x, q x :=
     and.elim_right hpq,
   assume x : α,
   show p x ∧ q x, from
     and.intro (hp x) (hq x))

/- 1.4. Reuse, if possible, the lemma `forall_and` you proved above to prove
the following instance of the lemma. -/

lemma forall_and_inst {α : Type} (r s : α → α → Prop) :
  (∀x, r x x ∧ s x x) ↔ (∀x, r x x) ∧ (∀x, s x x) :=
forall_and (λx, r x x) (λx, s x x)


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      `(a + b) * (a + b)`
    `= a * (a + b) + b * (a + b)`
    `= a * a + a * b + b * a + b * b`
    `= a * a + a * b + a * b + b * b`
    `= a * a + 2 * a * b + b * b`

Hint: You might need the tactics `simp` and `cc` and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
calc  (a + b) * (a + b)
    = a * (a + b) + b * (a + b) :
  begin
    simp [add_mul, mul_add],
    cc
  end
... = a * a + a * b + b * a + b * b :
  begin
    simp [add_mul, mul_add],
    cc
  end
... = a * a + a * b + a * b + b * b :
  by cc
... = a * a + 2 * a * b + b * b :
  begin
    simp [two_mul, mul_add, add_mul],
    cc
  end

/- 2.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
have h1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
  begin
    simp [add_mul, mul_add],
    cc
  end,
have h2 : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
  begin
    simp [add_mul, mul_add],
    cc
  end,
have h3 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
  begin
    simp,
    cc
  end,
have h4 : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
  begin
    simp [two_mul, add_mul, mul_add],
    cc
  end,
show _, from
  begin
    rw h1,
    rw h2,
    rw h3,
    rw h4
  end

/- 2.3. Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  simp [two_mul, add_mul, mul_add],
  cc
end


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom forall.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∀x : α, x = t ∧ p x) ↔ p t

lemma proof_of_false :
  false :=
begin
  have wrong : (∀x, x = 0 ∧ true) ↔ true :=
    @forall.one_point_wrong ℕ 0 (λ_, true),
  simp at wrong,
  have one_eq_zero : 1 = 0 :=
    wrong 1,
  cc
end

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a tactical or structured proof. -/

axiom exists.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t → p x) ↔ p t

lemma proof_of_false₂ :
  false :=
begin
  have wrong : (∃x, x ≠ 0) ↔ false :=
    @exists.one_point_wrong ℕ 0 (λ_, false),
  simp at wrong,
  have one_eq_zero : 1 = 0 :=
    wrong 1,
  cc
end

end LoVe
