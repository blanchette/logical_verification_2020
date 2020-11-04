import .love01_definitions_and_statements_demo


/- # LoVe Demo 3: Forward Proofs

When developing a proof, often it makes sense to work __forward__: to start with
what we already know and proceed step by step towards our goal. Lean's
structured proofs and raw proof terms are two style that support forward
reasoning. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace forward_proofs


/- ## Structured Constructs

Structured proofs are syntactic sugar sprinkled on top of Lean's
__proof terms__.

The simplest kind of structured proof is the name of a lemma, possibly with
arguments. -/

lemma add_comm (m n : ℕ) :
  add m n = add n m :=
sorry

lemma add_comm_zero_left (n : ℕ) :
  add 0 n = add n 0 :=
add_comm 0 n

lemma add_comm_zero_left₂ (n : ℕ) :
  add 0 n = add n 0 :=
by exact add_comm 0 n

/- `fix` and `assume` move `∀`-quantified variables and assumptions from the
goal into the local context. They can be seen as structured versions of the
`intros` tactic.

`show` repeats the goal to prove. It is useful as documentation or to rephrase
the goal (up to computation). -/

lemma fst_of_two_props :
  ∀a b : Prop, a → b → a :=
fix a b : Prop,
assume ha : a,
assume hb : b,
show a, from
  ha

lemma fst_of_two_props₂ (a b : Prop) (ha : a) (hb : b) :
  a :=
show a, from
  begin
    exact ha
  end

lemma fst_of_two_props₃ (a b : Prop) (ha : a) (hb : b) :
  a :=
ha

/- `have` proves an intermediate lemma, which can refer to the local context. -/

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
assume ha : a,
have hb : b :=
  hab ha,
have hc : c :=
  hbc hb,
show c, from
  hc

lemma prop_comp₂ (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
assume ha : a,
show c, from
  hbc (hab ha)


/- ## Forward Reasoning about Connectives and Quantifiers -/

lemma and_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
assume hab : a ∧ b,
have ha : a :=
  and.elim_left hab,
have hb : b :=
  and.elim_right hab,
show b ∧ a, from
  and.intro hb ha

lemma or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
assume hab : a ∨ b,
show b ∨ a, from
  or.elim hab
    (assume ha : a,
     show b ∨ a, from
       or.intro_right b ha)
    (assume hb : b,
     show b ∨ a, from
       or.intro_left a hb)

def double (n : ℕ) : ℕ :=
n + n

lemma nat_exists_double_iden :
  ∃n : ℕ, double n = n :=
exists.intro 0
  (show double 0 = 0, from
     by refl)

lemma nat_exists_double_iden₂ :
  ∃n : ℕ, double n = n :=
exists.intro 0 (by refl)

lemma modus_ponens (a b : Prop) :
  (a → b) → a → b :=
assume hab : a → b,
assume ha : a,
show b, from
  hab ha

lemma not_not_intro (a : Prop) :
  a → ¬¬ a :=
assume ha : a,
assume hna : ¬ a,
show false, from
  hna ha

lemma forall.one_point {α : Type} (t : α) (p : α → Prop) :
  (∀x, x = t → p x) ↔ p t :=
iff.intro
  (assume hall : ∀x, x = t → p x,
   show p t, from
     begin
       apply hall t,
       refl
     end)
  (assume hp : p t,
   fix x,
   assume heq : x = t,
   show p x, from
     begin
       rw heq,
       exact hp
     end)

lemma beast_666 (beast : ℕ) :
  (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
forall.one_point _ _

#print beast_666

lemma exists.one_point {α : Type} (t : α) (p : α → Prop) :
  (∃x : α, x = t ∧ p x) ↔ p t :=
iff.intro
  (assume hex : ∃x, x = t ∧ p x,
   show p t, from
     exists.elim hex
       (fix x,
        assume hand : x = t ∧ p x,
        show p t, from
          by cc))
  (assume hp : p t,
   show ∃x : α, x = t ∧ p x, from
     exists.intro t
       (show t = t ∧ p t, from
          by cc))


/- ## Calculational Proofs

In informal mathematics, we often use transitive chains of equalities,
inequalities, or equivalences (e.g., `a ≥ b ≥ c`). In Lean, such calculational
proofs are supported by `calc`.

Syntax:

    calc      _term₀_
        _op₁_ _term₁_ :
      _proof₁_
    ... _op₂_ _term₂_ :
      _proof₂_
     ⋮
    ... _opN_ _termN_ :
      _proofN_ -/

lemma two_mul_example (m n : ℕ) :
  2 * m + n = m + n + m :=
calc  2 * m + n
    = (m + m) + n :
  by rw two_mul
... = m + n + m :
  by cc

/- `calc` saves some repetition, some `have` labels, and some transitive
reasoning: -/

lemma two_mul_example₂ (m n : ℕ) :
  2 * m + n = m + n + m :=
have h₁ : 2 * m + n = (m + m) + n :=
  by rw two_mul,
have h₂ : (m + m) + n = m + n + m :=
  by cc,
show _, from
  eq.trans h₁ h₂


/- ## Forward Reasoning with Tactics

The `have`, `let`, and `calc` structured proof commands are also available as a
tactic. Even in tactic mode, it can be useful to state intermediate results and
definitions in a forward fashion.

Observe that the syntax for the tactic `let` is slightly different than for the
structured proof command `let`, with `,` instead of `in`. -/

lemma prop_comp₃ (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
begin
  intro ha,
  have hb : b :=
    hab ha,
  let c' := c,
  have hc : c' :=
    hbc hb,
  exact hc
end


/- ## Dependent Types

Dependent types are the defining feature of the dependent type theory family of
logics.

Consider a function `pick` that take a number `n : ℕ` and that returns a number
between 0 and `n`. Conceptually, `pick` has a dependent type, namely

    `(n : ℕ) → {i : ℕ // i ≤ n}`

We can think of this type as a `ℕ`-indexed family, where each member's type may
depend on the index:

    `pick n : {i : ℕ // i ≤ n}`

But a type may also depend on another type, e.g., `list` (or `λα, list α`) and
`λα, α → α`.

A term may depend on a type, e.g., `λα, λx : α, x` (a polymorphic identity
function).

Of course, a term may also depend on a term.

Unless otherwise specified, a __dependent type__ means a type depending on a
term. This is what we mean when we say that simple type theory does not support
dependent types.

In summary, there are four cases for `λx, t` in the calculus of inductive
constructions (cf. Barendregt's `λ`-cube):

Body (`t`) |              | Argument (`x`) | Description
---------- | ------------ | -------------- | ------------------------------
A term     | depending on | a term         | Simply typed `λ`-expression
A type     | depending on | a term         | Dependent type (strictly speaking)
A term     | depending on | a type         | Polymorphic term
A type     | depending on | a type         | Type constructor

Revised typing rules:

    C ⊢ t : (x : σ) → τ[x]    C ⊢ u : σ
    ———————————————————————————————————— App'
    C ⊢ t u : τ[u]

    C, x : σ ⊢ t : τ[x]
    ———————————————————————————————— Lam'
    C ⊢ (λx : σ, t) : (x : σ) → τ[x]

These two rules degenerate to `App` and `Lam` if `x` does not occur in `τ[x]`

Example of `App'`:

    ⊢ pick : (x : ℕ) → {y : ℕ // y ≤ x}    ⊢ 5 : ℕ
    ——————————————————————————————————————————————— App'
    ⊢ pick 5 : {y : ℕ // y ≤ 5}

Example of `Lam'`:

    α : Type, x : α ⊢ x : α
    ——————————————————————————————— Lam or Lam'
    α : Type ⊢ (λx : α, x) : α → α
    ————————————————————————————————————————————— Lam'
    ⊢ (λα : Type, λx : α, x) : (α : Type) → α → α

Regrettably, the intuitive syntax `(x : σ) → τ` is not available in Lean.
Instead, we must write `∀x : σ, τ` to specify a dependent type.

Aliases:

    `σ → τ` := `∀_ : σ, τ`
    `Π`     := `∀`


## The Curry–Howard Correspondence

`→` is used both as the implication symbol and as the type constructor of
functions. Similarly, `∀` is used both as a quantifier and in dependent types.

The two pairs of concepts not only look the same, they are the same, by the PAT
principle:

* PAT = propositions as types;
* PAT = proofs as terms.

This is also called the Curry–Howard correspondence.

Types:

* `σ → τ` is the type of total functions from `σ` to `τ`;
* `∀x : σ, τ[x]` is the dependent function type from `x : σ` to `τ[x]`.

Propositions:

* `P → Q` can be read as "`P` implies `Q`", or as the type of functions mapping
  proofs of `P` to proofs of `Q`.
* `∀x : σ, Q[x]` can be read as "for all `x`, `Q[x]`", or as the type of
  functions mapping values `x` of type `σ` to proofs of `Q[x]`.

Terms:

* A constant is a term.
* A variable is a term.
* `t u` is the application of function `t` to value `u`.
* `λx, t[x]` is a function mapping `x` to `t[x]`.

Proofs:

* A lemma or hypothesis name is a proof.
* `H t`, which instantiates the leading parameter or quantifier of proof `H`'
  statement with term `t`, is a proof.
* `H G`, which discharges the leading assumption of `H`'s statement with
  proof `G`, is a proof.
* `λh : P, H[h]` is a proof of `P → Q`, assuming `H[h]` is a proof of `Q`
  for `h : P`.
* `λx : σ, H[x]` is a proof of `∀x : σ, Q[x]`, assuming `H[x]` is a proof of
  `Q[x]` for `x : σ`. -/

lemma and_swap₃ (a b : Prop) :
  a ∧ b → b ∧ a :=
λhab : a ∧ b, and.intro (and.elim_right hab) (and.elim_left hab)

lemma and_swap₄ (a b : Prop) :
  a ∧ b → b ∧ a :=
begin
  intro hab,
  apply and.intro,
  apply and.elim_right,
  exact hab,
  apply and.elim_left,
  exact hab
end

/- Tactical proofs are reduced to proof terms. -/

#print and_swap₃
#print and_swap₄

end forward_proofs


/- ## Induction by Pattern Matching

By the Curry–Howard correspondence, a proof by induction is the same as a
recursively specified proof term. Thus, as alternative to the `induction'`
tactic, induction can also be done by pattern matching:

 * the induction hypothesis is then available under the name of the lemma we are
   proving;

 * well-foundedness of the argument is often proved automatically. -/

#check reverse

lemma reverse_append {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
| []        ys := by simp [reverse]
| (x :: xs) ys := by simp [reverse, reverse_append xs]

lemma reverse_append₂ {α : Type} (xs ys : list α) :
  reverse (xs ++ ys) = reverse ys ++ reverse xs :=
begin
  induction' xs,
  { simp [reverse] },
  { simp [reverse, ih] }
end

lemma reverse_reverse {α : Type} :
  ∀xs : list α, reverse (reverse xs) = xs
| []        := by refl
| (x :: xs) :=
  by simp [reverse, reverse_append, reverse_reverse xs]

end LoVe
