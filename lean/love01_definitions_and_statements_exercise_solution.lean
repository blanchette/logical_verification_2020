import .love01_definitions_and_statements_demo


/- # LoVe Exercise 1: Definitions and Statements

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Truncated Subtraction

1.1. Define the function `sub` that implements truncated subtraction on natural
numbers by recursion. "Truncated" means that results that mathematically would
be negative are represented by 0. For example:

    `sub 7 2 = 5`
    `sub 2 7 = 0` -/

def sub : ℕ → ℕ → ℕ
| m            0            := m
| 0            _            := 0
| (nat.succ m) (nat.succ n) := sub m n

/- 1.2. Check that your function works as expected. -/

#eval sub 0 0   -- expected: 0
#eval sub 0 1   -- expected: 0
#eval sub 0 7   -- expected: 0
#eval sub 1 0   -- expected: 1
#eval sub 1 1   -- expected: 0
#eval sub 3 0   -- expected: 3
#eval sub 2 7   -- expected: 0
#eval sub 3 1   -- expected: 2
#eval sub 3 3   -- expected: 0
#eval sub 3 7   -- expected: 0
#eval sub 7 2   -- expected: 5


/- ## Question 2: Arithmetic Expressions

Consider the type `aexp` from the lecture and the function `eval` that
computes the value of an expression. You will find the definitions in the file
`love01_definitions_and_statements_demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `aexp` or `eval`;
3. click the identifier. -/

#check aexp
#check eval

/- 2.1. Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Make sure to use `#eval`. For technical reasons, `#reduce` does not work well
here. Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `aexp`) are unrelated. -/

def some_env : string → ℤ
| "x" := 3
| "y" := 17
| _   := 201

#eval eval some_env (aexp.var "x")   -- expected: 3
#eval eval some_env (aexp.num 12)                              -- expected: 12
#eval eval some_env (aexp.add (aexp.var "x") (aexp.var "y"))   -- expected: 20
#eval eval some_env (aexp.sub (aexp.num 5) (aexp.var "y"))     -- expected: -12
#eval eval some_env (aexp.mul (aexp.num 11) (aexp.var "z"))    -- expected: 2211
#eval eval some_env (aexp.div (aexp.num 2) (aexp.num 0))       -- expected: 0

/- 2.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : aexp → aexp
| (aexp.add (aexp.num 0) e₂) := simplify e₂
| (aexp.add e₁ (aexp.num 0)) := simplify e₁
| (aexp.sub e₁ (aexp.num 0)) := simplify e₁
| (aexp.mul (aexp.num 0) e₂) := aexp.num 0
| (aexp.mul e₁ (aexp.num 0)) := aexp.num 0
| (aexp.mul (aexp.num 1) e₂) := simplify e₂
| (aexp.mul e₁ (aexp.num 1)) := simplify e₁
| (aexp.div (aexp.num 0) e₂) := aexp.num 0
| (aexp.div e₁ (aexp.num 0)) := aexp.num 0
| (aexp.div e₁ (aexp.num 1)) := simplify e₁
-- catch-all cases below
| (aexp.num i)               := aexp.num i
| (aexp.var x)               := aexp.var x
| (aexp.add e₁ e₂)           := aexp.add (simplify e₁) (simplify e₂)
| (aexp.sub e₁ e₂)           := aexp.sub (simplify e₁) (simplify e₂)
| (aexp.mul e₁ e₂)           := aexp.mul (simplify e₁) (simplify e₂)
| (aexp.div e₁ e₂)           := aexp.div (simplify e₁) (simplify e₂)

/- 2.3. State (without proving it) the correctness lemma for `simplify`, namely
that the simplified expression should have the same semantics, with respect to
`eval`, as the original expression. -/

lemma simplify_correct (env : string → ℤ) (e : aexp) :
  eval env (simplify e) = eval env e :=
sorry


/- ## Question 3: λ-Terms

3.1. Complete the following definitions, by replacing the `sorry` markers by
terms of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
λa, a

def K : α → β → α :=
λa b, a

def C : (α → β → γ) → β → α → γ :=
λg b a, g a b

def proj_1st : α → α → α :=
λx y, x

/- Please give a different answer than for `proj_1st`. -/

def proj_2nd : α → α → α :=
λx y, y

def some_nonsense : (α → β → γ) → α → (α → γ) → β → γ :=
λg a f b, g a b

/- 3.2. Show the typing derivation for your definition of `C` above, on paper
or using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful. -/

/- Let `D` := `g : α → β → γ, b : β, a : α`. We have

    –––––––––––––––––– Var    –––––––––– Var
    D ⊢ g : α → β → γ         D ⊢ a : α
    –––––––––––––––––––––––––––––––––––– App    –––––––––– Var
    D ⊢ g a : β → γ                             D ⊢ b : β
    –––––––––––––––––––––––––––––––––––––––––––––––––––––– App
    D ⊢ g a b : γ
    ––––––––––––––––––––––––––––––––––––––––––– Lam
    g : α → β → γ, b : β ⊢ (λa : α, g a b) : γ
    –––––––––––––––––––––––––––––––––––––––––––––– Lam
    g : α → β → γ ⊢ (λ(b : β) (a : α), g a b) : γ
    ––––––––––––––––––––––––––––––––––––––––––––––– Lam
    ⊢ (λ(g : α → β → γ) (b : β) (a : α), g a b) : γ -/

end LoVe
