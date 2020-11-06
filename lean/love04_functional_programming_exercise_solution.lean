import .love03_forward_proofs_demo


/- # LoVe Exercise 4: Functional Programming -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Reverse of a List

We define a new accumulator-based version of `reverse`. The first argument,
`as`, serves as the accumulator. This definition is __tail-recursive__, meaning
that compilers and interpreters can easily optimize the recursion away,
resulting in more efficient code. -/

def accurev {α : Type} : list α → list α → list α
| as []        := as
| as (x :: xs) := accurev (x :: as) xs

/- 1.1. Our intention is that `accurev [] xs` should be equal to `reverse xs`.
But if we start an induction, we quickly see that the induction hypothesis is
not strong enough. Start by proving the following generalization (using the
`induction'` tactic or pattern matching): -/

lemma accurev_eq_reverse_append {α : Type} :
  ∀as xs : list α, accurev as xs = reverse xs ++ as
| as []        := by refl
| as (x :: xs) := by simp [reverse, accurev, accurev_eq_reverse_append _ xs]

/- 1.2. Derive the desired equation. -/

lemma accurev_eq_reverse {α : Type} (xs : list α) :
  accurev [] xs = reverse xs :=
by simp [accurev_eq_reverse_append]

/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

lemma accurev_accurev {α : Type} (xs : list α) :
  accurev [] (accurev [] xs) = xs :=
by simp [accurev_eq_reverse, reverse_reverse]

/- 1.4. Prove the following lemma by structural induction, as a "paper" proof.
This is a good exercise to develop a deeper understanding of how structural
induction works (and is good practice for the final exam).

    lemma accurev_eq_reverse_append {α : Type} :
      ∀as xs : list α, accurev as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `cc` need
not be justified if you think they are obvious (to humans), but you should say
which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

/- We perform the proof by structural induction on `xs`, generalizing `as`.

Case `[]`: The goal is `accurev as [] = reverse [] ++ as`. The left-hand side
is `as` by definition of `accurev`. The right-hand side is `as` by definition
of `reverse` and `++`.

Case `x :: xs`: The goal is `accurev as (x :: xs) = reverse (x :: xs) ++ as`.
The induction hypothesis is `∀as, accurev as xs = reverse xs ++ as`.

Let us simplify the goal's left-hand side:

      accurev as (x :: xs)
    = accurev (x :: as) xs        -- by definition of `accurev`
    = reverse xs ++ (x :: as)     -- by the induction hypothesis

Now let us massage the right-hand side so that it matches the simplified
left-hand side:

      reverse (x :: xs) ++ as
    = (reverse xs ++ [x]) ++ as   -- by definition of `reverse`
    = reverse xs ++ ([x] ++ as)   -- by associativity of `++`
    = reverse xs ++ (x :: as)     -- by definition of `++`

The two sides are equal. QED -/


/- ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → list α → list α
| 0       xs        := xs
| (_ + 1) []        := []
| (m + 1) (x :: xs) := drop m xs

/- Its relative `take` returns a list consisting of the the first `n` elements
at the front of a list.

2.1. Define `take`.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → list α → list α
| 0       _         := []
| (_ + 1) []        := []
| (m + 1) (x :: xs) := x :: take m xs

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following lemmas, using `induction'` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] lemma drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : list α) = []
| 0       := by refl
| (_ + 1) := by refl

@[simp] lemma take_nil {α : Type} :
  ∀n : ℕ, take n ([] : list α) = []
| 0       := by refl
| (_ + 1) := by refl

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following lemmas. In other words, for each lemma, there should be three cases,
and the third case will need to invoke the induction hypothesis.

The first case is shown for `drop_drop`. Beware of the fact that there are three
variables in the `drop_drop` lemma (but only two arguments to `drop`).

Hint: The `refl` tactic might be useful in the third case of `drop_drop`. -/

lemma drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0       n xs        := by refl
| (_ + 1) _ []        := by simp [drop]
| (m + 1) n (x :: xs) :=
  begin
    simp [drop, drop_drop m n xs],
    refl
  end

lemma take_take {α : Type} :
  ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs
| 0       _         := by refl
| (_ + 1) []        := by refl
| (m + 1) (x :: xs) := by simp [take, take_take m xs]

lemma take_drop {α : Type} :
  ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0       _         := by refl
| (_ + 1) []        := by refl
| (m + 1) (x :: xs) := by simp [take, drop, take_drop m]


/- ## Question 3: A Type of λ-Terms

3.1. Define an inductive type corresponding to the untyped λ-terms, as given
by the following context-free grammar:

    term ::= 'var' string        -- variable (e.g., `x`)
           | 'lam' string term   -- λ-expression (e.g., `λx, t`)
           | 'app' term term     -- application (e.g., `t u`) -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/- 3.2. Register a textual representation of the type `term` as an instance of
the `has_repr` type class. Make sure to supply enough parentheses to guarantee
that the output is unambiguous. -/

def term.repr : term → string
| (term.var s)   := s
| (term.lam s t) := "(λ" ++ s ++ ", " ++ term.repr t ++ ")"
| (term.app t u) := "(" ++ term.repr t ++ " " ++ term.repr u ++ ")"

@[instance] def term.has_repr : has_repr term :=
{ repr := term.repr }

/- 3.3. Test your textual representation: -/

#eval (term.lam "x" (term.app (term.app (term.var "y") (term.var "x"))
    (term.var "x")))
  -- should print something like `(λx, ((y x) x))`

end LoVe
