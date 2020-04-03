import .love01_definitions_and_statements_demo


/-! # LoVe Demo 2: Backward Proofs

A __tactic__ operates on a proof goal and either proves it or creates new
subgoals. Tactics are a __backward__ proof mechanism: They start from the goal
and work towards the available hypotheses and lemmas. -/


set_option pp.beta true

namespace LoVe


/-! ## Tactic Mode

Syntax of tactical proofs:

    begin
      _tactic₁_,
      …,
      _tacticN_
    end -/

lemma fst_of_two_props :
  ∀a b : Prop, a → b → a :=
begin
  intros a b,
  intros ha hb,
  apply ha
end

/-! ## Basic Tactics

`intro`(`s`) moves `∀`-quantified variables, or the assumptions of
implications `→`, from the goal's conclusion (after `⊢`) into the goal's
hypotheses (before `⊢`).

`apply` matches the goal's conclusion with the conclusion of the specified lemma
and adds the lemma's hypotheses as new goals. -/

lemma fst_of_two_props₂ (a b : Prop) (ha : a) (hb : b) :
  a :=
begin
  apply ha
end

/-! Terminal tactic syntax:

    by _tactic_

abbreviates

    begin
      _tactic_
    end -/

lemma fst_of_two_props₃ (a b : Prop) (ha : a) (hb : b) :
  a :=
by apply ha

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
begin
  intro ha,
  apply hbc,
  apply hab,
  apply ha
end

/-! `exact` matches the goal's conclusion with the specified lemma, closing the
goal. We can often use `apply` in such situations, but `exact` communicates our
intentions better. -/

lemma fst_of_two_props₄ (a b : Prop) (ha : a) (hb : b) :
  a :=
by exact ha

/-! `assumption` finds a hypothesis from the local context that matches the
goal's conclusion and applies it to prove the goal. -/

lemma fst_of_two_props₅ (a b : Prop) (ha : a) (hb : b) :
  a :=
by assumption

/-! `refl` proves `l = r`, where the two sides are equal up to computation.
Computation means unfolding of definitions, β-reduction (application of λ to an
argument), `let`, and more. -/

lemma α_example {α β : Type} (f : α → β) :
  (λx, f x) = (λy, f y) :=
begin
  refl
end

lemma α_example₂ {α β : Type} (f : α → β) :
  (λx, f x) = (λy, f y) :=
by refl

lemma β_example {α β : Type} (f : α → β) (a : α) :
  (λx, f x) a = f a :=
by refl

def double (n : ℕ) : ℕ :=
n + n

lemma δ_example :
  double 5 = 5 + 5 :=
by refl

lemma ζ_example :
  (let n : ℕ := 2 in n + n) = 4 :=
by refl

lemma η_example {α β : Type} (f : α → β) :
  (λx, f x) = f :=
by refl

lemma ι_example {α β : Type} (a : α) (b : β) :
  prod.fst (a, b) = a :=
by refl


/-! ## Reasoning about Logical Connectives and Quantifiers

Introduction rules: -/

#check true.intro
#check not.intro
#check and.intro
#check or.intro_left
#check or.intro_right
#check iff.intro
#check exists.intro

/-! Elimination rules: -/

#check false.elim
#check and.elim_left
#check and.elim_right
#check or.elim
#check iff.elim_left
#check iff.elim_right
#check exists.elim

/-! Definition of `¬` and related lemmas: -/

#print not
#check not_def
#check classical.em
#check classical.by_contradiction

lemma and_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
begin
  intro hab,
  apply and.intro,
  apply and.elim_right,
  exact hab,
  apply and.elim_left,
  exact hab
end

/-! The `{ … }` combinator focuses on the first subgoal. The tactic inside must
fully prove it. -/

lemma and_swap₂ :
  ∀a b : Prop, a ∧ b → b ∧ a :=
begin
  intros a b hab,
  apply and.intro,
  { exact and.elim_right hab },
  { exact and.elim_left hab }
end

/-! Notice above how we pass the hypothesis `hab` directly to the lemmas
`and.elim_right` and `and.elim_left`, instead of waiting for the lemmas's
assumptions to appear as new subgoals. This is a small forward step in an
otherwise backward proof. -/

lemma or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
begin
  intros hab,
  apply or.elim hab,
  { intros ha,
    exact or.intro_right _ ha },
  { intros hb,
    exact or.intro_left _ hb }
end

lemma modus_ponens (a b : Prop) :
  (a → b) → a → b :=
begin
  intros hab ha,
  apply hab,
  exact ha
end

lemma not_not_intro (a : Prop) :
  a → ¬¬ a :=
begin
  intro ha,
  apply not.intro,
  intro hna,
  apply hna,
  exact ha
end

lemma not_not_intro₂ (a : Prop) :
  a → ¬¬ a :=
begin
  intros ha hna,
  apply hna,
  exact ha
end

lemma nat_exists_double_iden :
  ∃n : ℕ, double n = n :=
begin
  apply exists.intro 0,
  refl
end


/-! ## Reasoning about Equality -/

#check eq.refl
#check eq.symm
#check eq.trans
#check eq.subst

/-! The above rules can be used directly: -/

lemma cong_fst_arg {α : Type} (a a' b : α)
    (f : α → α → α) (ha : a = a') :
  f a b = f a' b :=
begin
  apply eq.subst ha,
  apply eq.refl
end

lemma cong_two_args {α : Type} (a a' b b' : α)
    (f : α → α → α) (ha : a = a') (hb : b = b') :
  f a b = f a' b' :=
begin
  apply eq.subst ha,
  apply eq.subst hb,
  apply eq.refl
end

/-! `rewrite` applies a single equation as a left-to-right rewrite rule, once.
To apply an equation right-to-left, prefix its name with `←`. -/

lemma cong_two_args₂ {α : Type} (a a' b b' : α)
    (f : α → α → α) (ha : a = a') (hb : b = b') :
  f a b = f a' b' :=
begin
  rewrite ha,
  rewrite hb
end

lemma a_proof_of_negation₃ (a : Prop) :
  a → ¬¬ a :=
begin
  rewrite not_def,
  rewrite not_def,
  intro ha,
  apply not.intro,
  intro hna,
  apply hna,
  exact ha
end

/-! `simp` applies a standard set of rewrite rules (the __simp set__)
exhaustively. The set can be extended using the `@[simp]` attribute. Lemmas can
be temporarily added to the simp set with the syntax
`simp [_lemma₁_, …, _lemmaN_]`. -/

lemma cong_two_args_etc {α : Type} (a a' b b' : α)
    (g : α → α → ℕ → α) (ha : a = a') (hb : b = b') :
  g a b (1 + 1) = g a' b' 2 :=
by simp [ha, hb]

/-! `cc` applies __congruence closure__ to derive new equalities. -/

lemma cong_two_args₃ {α : Type} (a a' b b' : α)
    (f : α → α → α) (ha : a = a') (hb : b = b') :
  f a b = f a' b' :=
by cc

/-! `cc` can also reason up to associativity and commutativity of `+`, `*`,
and other binary operators. -/

lemma cong_assoc_comm (a a' b c : ℝ) (f : ℝ → ℝ)
    (ha : a = a') :
  f (a + b + c) = f (c + b + a') :=
by cc


/-! ## Proofs by Mathematical Induction

`induction` performs induction on the specified variable. It gives rise to one
subgoal per constructor. -/

lemma add_zero (n : ℕ) :
  add 0 n = n :=
begin
  induction n,
  { refl },
  { simp [add, n_ih] }
end

lemma add_succ (m n : ℕ) :
  add (nat.succ m) n = nat.succ (add m n) :=
begin
  induction n,
  { refl },
  { simp [add, n_ih] }
end

lemma add_comm (m n : ℕ) :
  add m n = add n m :=
begin
  induction n,
  { simp [add, add_zero] },
  { simp [add, add_succ, n_ih] }
end

lemma add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
begin
  induction n,
  { refl },
  { simp [add, n_ih] }
end

/-! `cc` is extensible. We can register `add` as a commutative and associative
operator using the type class instance mechanism (explained in lecture 11). This
is useful for the `cc` invocation below. -/

@[instance] def add.is_commutative : is_commutative ℕ add :=
{ comm := add_comm }

@[instance] def add.is_associative : is_associative ℕ add :=
{ assoc := add_assoc }

lemma mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
begin
  induction n,
  { refl },
  { simp [add, mul, n_ih],
    cc }
end


/-! ## Cleanup Tactics

`rename` changes the name of a variable or hypothesis.

`clear` removes unused variables or hypotheses. -/

lemma cleanup_example (a b c : Prop) (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) :
  c :=
begin
  clear ha hab a,
  apply hbc,
  clear hbc c,
  rename hb h,
  exact h
end

end LoVe
