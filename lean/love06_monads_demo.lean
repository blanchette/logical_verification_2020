import .lovelib


/- # LoVe Demo 6: Monads

We take a look at an important functional programming abstraction: monads.
Monads generalize computation with side effects. Haskell has shown that monads
can be used very successful to write imperative programs. For us, they are
interesting in their own right and for two more reasons:

* They provide a nice example of axiomatic reasoning.

* They are useful for programming Lean itself (metaprogramming, lecture 7). -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Introductory Example

Consider the following programming task:

    Implement a function `sum_2_5_7 ns` that sums up the second, fifth, and
    seventh items of a list `ns` of natural numbers. Use `option ℕ` for the
    result so that if the list has fewer than seven elements, you can return
    `option.none`.

A straightforward solution follows: -/

def sum_2_5_7 (ns : list ℕ) : option ℕ :=
match list.nth ns 1 with
| option.none    := option.none
| option.some n2 :=
  match list.nth ns 4 with
  | option.none    := option.none
  | option.some n5 :=
    match list.nth ns 6 with
    | option.none    := option.none
    | option.some n7 := option.some (n2 + n5 + n7)
    end
  end
end

/- The code is ugly, because of all the pattern matching on options.

We can put all the ugliness in one function, which we call `connect`: -/

def connect {α : Type} {β : Type} :
  option α → (α → option β) → option β
| option.none     f := option.none
| (option.some a) f := f a

def sum_2_5_7₂ (ns : list ℕ) : option ℕ :=
connect (list.nth ns 1)
  (λn2, connect (list.nth ns 4)
     (λn5, connect (list.nth ns 6)
        (λn7, option.some (n2 + n5 + n7))))

/- Instead of defining `connect` ourselves, we can use Lean's predefined
general `bind` operation. We can also use `pure` instead of `option.some`: -/

#check bind

def sum_2_5_7₃ (ns : list ℕ) : option ℕ :=
bind (list.nth ns 1)
  (λn2, bind (list.nth ns 4)
     (λn5, bind (list.nth ns 6)
        (λn7, pure (n2 + n5 + n7))))

/- Syntactic sugar:

    `ma >>= f` := `bind ma f` -/

#check (>>=)

def sum_2_5_7₄ (ns : list ℕ) : option ℕ :=
list.nth ns 1 >>=
  λn2, list.nth ns 4 >>=
    λn5, list.nth ns 6 >>=
      λn7, pure (n2 + n5 + n7)

/- Syntactic sugar:

    `do a ← ma, t` := `ma >>= (λa, t)`
    `do ma, t`     := `ma >>= (λ_, t)` -/

def sum_2_5_7₅ (ns : list ℕ) : option ℕ :=
do n2 ← list.nth ns 1,
  do n5 ← list.nth ns 4,
    do n7 ← list.nth ns 6,
      pure (n2 + n5 + n7)

/- The `do`s can be combined: -/

def sum_2_5_7₆ (ns : list ℕ) : option ℕ :=
do
  n2 ← list.nth ns 1,
  n5 ← list.nth ns 4,
  n7 ← list.nth ns 6,
  pure (n2 + n5 + n7)

/- Although the notation has an imperative flavor, the function is a pure
functional program.


## Two Operations and Three Laws

The `option` type constructor is an example of a monad.

In general, a __monad__ is a type constructor `m` that depends on some type
parameter `α` (i.e., `m α`) equipped with two distinguished operations:

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

For `option`:

    `pure` := `option.some`
    `bind` := `connect`

Intuitively, we can think of a monad as a "box":

* `pure` puts the data into the box.

* `bind` allows us to access the data in the box and modify it (possibly even
  changing its type, since the result is an `m β` monad, not a `m α` monad).

There is no general way to extract the data from the monad, i.e., to obtain an
`α` from an `m α`.

To summarize, `pure a` provides no side effect and simply provides a box
containing the the value `a`, whereas `bind ma f` (also written `ma >>= f`)
executes `ma`, then executes `f` with the boxed result `a` of `ma`.

The option monad is only one instance among many.

Type         | Effect
------------ | --------------------------------------------------------------
`id α`       | no effect
`option α`   | simple exceptions
`σ → α × σ`  | threading through a state of type `σ`
`set α`      | nondeterministic computation returning `α` values
`t → α`      | reading elements of type `t` (e.g., a configuration)
`ℕ × α`      | adjoining running time (e.g., to model algorithmic complexity)
`string × α` | adjoining text output (e.g., for logging)
`prob α`     | probability (e.g., using random number generators)
`io α`       | interaction with the operating system
`tactic α`   | interaction with the proof assistant

All of the above are type constructors `m` are parameterized by a type `α`.

Some effects can be combined (e.g., `option (t → α)`).

Some effects are not executable (e.g., `set α`, `prob α`). They are nonetheless
useful for modeling programs abstractly in the logic.

Specific monads may provide a way to extract the boxed value stored in the monad
without `bind`'s requirement of putting it back in a monad.

Monads have several benefits, including:

* They provide the convenient and highly readable `do` notation.

* They support generic operations, such as
  `mmap {α β : Type} : (α → m β) → list α → m (list β)`, which work uniformly
  across all monads.

The `bind` and `pure` operations are normally required to obey three laws,
called the monad laws. Pure data as the first program can be simplified away:

    do
      a' ← pure a,
      f a'
  =
    f a

Pure data as the second program can be simplified away:

    do
      a ← ma,
      pure a
  =
    ma

Nested programs `ma`, `f`, `g` can be flattened using this associativity rule:

    do
      b ← do {
        a ← ma,
        f a },
      g b
  =
    do
      a ← ma,
      b ← f a,
      g b


## A Type Class of Monads

Monads are a mathematical structure, so we use class to add them as a type
class. We can think of a type class as a structure that is parameterized by a
type—or here, by a type constructor `m : Type → Type`. -/

@[class] structure lawful_monad (m : Type → Type)
  extends has_bind m, has_pure m :=
(pure_bind {α β : Type} (a : α) (f : α → m β) :
   (pure a >>= f) = f a)
(bind_pure {α : Type} (ma : m α) :
   (ma >>= pure) = ma)
(bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
     (ma : m α) :
   ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)))

#print monad
#print is_lawful_monad

/- Step by step:

* We are creating a structure parameterized by a unary type constructor `m`.

* The structure inherits the fields, and any syntactic sugar, from structures
  called `has_bind` and `has_pure`, which provide the `bind` and `pure`
  operations on `m` and some syntactic sugar.

* The definition adds three fields to those already provided by `has_bind` and
  `has_pure`, to store the proofs of the monad laws.

To instantiate this definition with a concrete monad, we must supply the type
constructor `m` (e.g., `option`), `bind` and `pure` operators, and
proofs of the monad laws.

(Lean's actual definition of monads is more complicated.)


## No Effects -/

def id.pure {α : Type} : α → id α :=
id

def id.bind {α β : Type} : id α → (α → id β) → id β
| a f := f a

@[instance] def id.lawful_monad : lawful_monad id :=
{ pure       := @id.pure,
  bind       := @id.bind,
  pure_bind  :=
    begin
      intros α β a f,
      refl
    end,
  bind_pure  :=
    begin
      intros α ma,
      refl
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      refl
    end }


/- ## Exceptions -/

def option.pure {α : Type} : α → option α :=
option.some

def option.bind {α β : Type} :
  option α → (α → option β) → option β
| option.none     f := option.none
| (option.some a) f := f a

@[instance] def option.lawful_monad : lawful_monad option :=
{ pure       := @option.pure,
  bind       := @option.bind,
  pure_bind  :=
    begin
      intros α β a f,
      refl
    end,
  bind_pure  :=
    begin
      intros α ma,
      cases' ma,
      { refl },
      { refl }
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      cases' ma,
      { refl },
      { refl }
    end }

def option.throw {α : Type} : option α :=
option.none

def option.catch {α : Type} :
  option α → option α → option α
| option.none     ma' := ma'
| (option.some a) _   := option.some a

@[instance] def option.has_orelse : has_orelse option :=
{ orelse := @option.catch }


/- ## Mutable State -/

def action (σ α : Type) :=
σ → α × σ

def action.read {σ : Type} : action σ σ
| s := (s, s)

def action.write {σ : Type} (s : σ) : action σ unit
| _ := ((), s)

def action.pure {σ α : Type} (a : α) : action σ α
| s := (a, s)

def action.bind {σ : Type} {α β : Type} (ma : action σ α)
    (f : α → action σ β) :
  action σ β
| s :=
  match ma s with
  | (a, s') := f a s'
  end

@[instance] def action.lawful_monad {σ : Type} :
  lawful_monad (action σ) :=
{ pure       := @action.pure σ,
  bind       := @action.bind σ,
  pure_bind  :=
    begin
      intros α β a f,
      apply funext,
      intro s,
      refl
    end,
  bind_pure  :=
    begin
      intros α ma,
      apply funext,
      intro s,
      simp [action.bind],
      cases' ma s,
      refl
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      apply funext,
      intro s,
      simp [action.bind],
      cases' ma s,
      refl
    end }

def diff_list : list ℕ → action ℕ (list ℕ)
| []        := pure []
| (n :: ns) :=
  do
    prev ← action.read,
    if n < prev then
      diff_list ns
    else
      do
        action.write n,
        ns' ← diff_list ns,
        pure (n :: ns')

#eval diff_list [1, 2, 3, 2] 0
#eval diff_list [1, 2, 3, 2, 4, 5, 2] 0


/- ## Nondeterminism -/

#check set

def set.pure {α : Type} : α → set α
| a := {a}

def set.bind {α β : Type} : set α → (α → set β) → set β
| A f := {b | ∃a, a ∈ A ∧ b ∈ f a}

@[instance] def set.lawful_monad : lawful_monad set :=
{ pure       := @set.pure,
  bind       := @set.bind,
  pure_bind  :=
    begin
      intros α β a f,
      simp [set.pure, set.bind]
    end,
  bind_pure  :=
    begin
      intros α ma,
      simp [set.pure, set.bind]
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      simp [set.pure, set.bind],
      apply set.ext,
      simp,
      tautology
    end }

/- `tautology` performs elimination of the logical symbols `∧`, `∨`, `↔`, and
`∃` in hypotheses and introduction of `∧`, `↔`, and `∃` in the conclusion, until
all the emerging subgoals can be trivially proved (e.g., by `refl`).


## A Generic Algorithm: Iteration over a List -/

def mmap {m : Type → Type} [lawful_monad m] {α β : Type}
    (f : α → m β) :
  list α → m (list β)
| []        := pure []
| (a :: as) :=
  do
    b ← f a,
    bs ← mmap as,
    pure (b :: bs)

lemma mmap_append {m : Type → Type} [lawful_monad m]
    {α β : Type} (f : α → m β) :
  ∀as as' : list α, mmap f (as ++ as') =
    do
      bs ← mmap f as,
      bs' ← mmap f as',
      pure (bs ++ bs')
| []        _   :=
  by simp [mmap, lawful_monad.bind_pure, lawful_monad.pure_bind]
| (a :: as) as' :=
  by simp [mmap, mmap_append as as', lawful_monad.pure_bind,
    lawful_monad.bind_assoc]

def nths {α : Type} (xss : list (list α)) (n : ℕ) :
  option (list α) :=
mmap (λxs, list.nth xs n) xss

#eval nths
  [[11, 12, 13, 14],
   [21, 22, 23],
   [31, 32, 33]] 2

end LoVe
