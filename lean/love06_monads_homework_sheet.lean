import .love06_monads_demo


/- # LoVe Homework 6: Monads

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (6 points): Better Exceptions

The __error monad__ is a monad stores either a value of type `α` or an error of
type `ε`. This corresponds to the following type: -/

inductive error (ε α : Type) : Type
| good {} : α → error
| bad {}  : ε → error

/- The error monad generalizes the option monad seen in the lecture. The `good`
constructor, corresponding to `option.some`, stores the current result of the
computation. But instead of having a single bad state `option.none`, the error
monad has many bad states of the form `bad e`, where `e` is an "exception" of
type `ε`.

1.1 (1 point). Implement a variant of `list.nth` that returns an error
message of the form "index _i_ out of range" instead of `option.none` on
failure.

Hint: For this, you will only need pattern matching (no monadic code). -/

#check list.nth

def list.nth_error {α : Type} (as : list α) (i : ℕ) : error string α :=
sorry

/- 1.2 (1 point). Complete the definitions of the `pure` and `bind` operations
on the error monad: -/

def error.pure {ε α : Type} : α → error ε α :=
sorry

def error.bind {ε α β : Type} : error ε α → (α → error ε β) → error ε β :=
sorry

/- The following type class instance makes it possible to use `>>=` and `do`
notations in conjunction with error monads: -/

@[instance] def error.monad {ε : Type} : monad (error ε) :=
{ pure := @error.pure ε,
  bind := @error.bind ε }

/- 1.3 (2 point). Prove the monad laws for the error monad. -/

lemma error.pure_bind {ε α β : Type} (a : α) (f : α → error ε β) :
  (pure a >>= f) = f a :=
sorry

lemma error.bind_pure {ε α : Type} (ma : error ε α) :
  (ma >>= pure) = ma :=
sorry

lemma error.bind_assoc {ε α β γ : Type} (f : α → error ε β) (g : β → error ε γ)
    (ma : error ε α) :
  ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)) :=
sorry

/- 1.4 (1 point). Define the following two operations on the error monad.

The `throw` operation raises an exception `e`, leaving the monad in a bad state
storing `e`.

The `catch` operation can be used to recover from an earlier exception. If the
monad is currently in a bad state storing `e`, `catch` invokes some
exception-handling code (the second argument to `catch`), passing `e` as
argument; this code might in turn raise a new exception. If `catch` is applied
to a good state, nothing happens—the monad remains in the good state. As a
convenient alternative to `error.catch ma g`, Lean lets us write
`ma.catch g`. -/

def error.throw {ε α : Type} : ε → error ε α :=
sorry

def error.catch {ε α : Type} : error ε α → (ε → error ε α) → error ε α :=
sorry

/- 1.5 (1 point). Using `list.nth_error` and the monadic operations on `error`,
and the special `error.catch` operation, write a monadic program that swaps the
values at indexes `i` and `j` in the input list `as`. If either of the indices
is out of range, return `as` unchanged. -/

def list.swap {α : Type} (as : list α) (i j : ℕ) : error string (list α) :=
sorry

#reduce list.swap [3, 1, 4, 1] 0 2   -- expected: error.good [4, 1, 3, 1]
#reduce list.swap [3, 1, 4, 1] 0 7   -- expected: error.good [3, 1, 4, 1]


/- ## Question 2 (3 points + 1 bonus point): Properties of `mmap`

We will prove some properties of the `mmap` function introduced in the
lecture's demo. -/

#check mmap

/- 2.1 (1 point). Prove the following identity law about `mmap` for an
arbitrary monad `m`.

Hint: You will need the lemma `lawful_monad.pure_bind` in the induction step. -/

lemma mmap_pure {m : Type → Type} [lawful_monad m] {α : Type} (as : list α) :
  mmap (@pure m _ _) as = pure as :=
sorry

/- Commutative monads are monads for which we can reorder actions that do not
depend on each others. Formally: -/

@[class] structure comm_lawful_monad (m : Type → Type)
  extends lawful_monad m : Type 1 :=
(bind_comm {α β γ δ : Type} (ma : m α) (f : α → m β) (g : α → m γ)
     (h : α → β → γ → m δ) :
   (ma >>= (λa, f a >>= (λb, g a >>= (λc, h a b c)))) =
   (ma >>= (λa, g a >>= (λc, f a >>= (λb, h a b c)))))

/- 2.2 (1 point). Prove that `option` is a commutative monad. -/

lemma option.bind_comm {α β γ δ : Type} (ma : option α) (f : α → option β)
    (g : α → option γ) (h : α → β → γ → option δ) :
  (ma >>= λa, f a >>= λb, g a >>= λc, h a b c) =
  (ma >>= λa, g a >>= λc, f a >>= λb, h a b c) :=
sorry

/- 2.3 (1 point). Explain why `error` is not a commutative monad. -/

-- enter your answer here

/- 2.4 (1 bonus point). Prove the following composition law for `mmap`, which
holds for commutative monads.

Hint: You will need structural induction. -/

lemma mmap_mmap {m : Type → Type} [comm_lawful_monad m]
    {α β γ : Type} (f : α → m β) (g : β → m γ) (as : list α) :
  (mmap f as >>= mmap g) = mmap (λa, f a >>= g) as :=
sorry

end LoVe
