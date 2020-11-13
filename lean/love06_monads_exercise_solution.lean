import .love06_monads_demo


/- # LoVe Exercise 6: Monads -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: A State Monad with Failure

We introduce a richer notion of lawful monad that provides an `orelse`
operator `<|>` satisfying some laws, given below. `emp` denotes failure.
`x <|> y` tries `x` first, falling back on `y` on failure. -/

@[class] structure lawful_monad_with_orelse (m : Type → Type)
  extends lawful_monad m, has_orelse m : Type 1 :=
(emp {} {α : Type} : m α)
(emp_orelse {α : Type} (a : m α) :
  (emp <|> a) = a)
(orelse_emp {α : Type} (a : m α) :
  (a <|> emp) = a)
(orelse_assoc {α : Type} (a b c : m α) :
  ((a <|> b) <|> c) = (a <|> (b <|> c)))
(emp_bind {α β : Type} (f : α → m β) :
  (emp >>= f) = emp)
(bind_emp {α β : Type} (f : m α) :
  (f >>= (λa, emp : α → m β)) = emp)

/- 1.1. We set up the `option` type constructor to be a
`lawful_monad_with_orelse`. Complete the proofs. -/

def option.orelse {α : Type} : option α → option α → option α
| option.none     ma' := ma'
| (option.some a) _   := option.some a

@[instance] def lawful_monad_with_orelse_option :
  lawful_monad_with_orelse option :=
{ emp          := λα, option.none,
  orelse       := @option.orelse,
  emp_orelse   :=
    begin
      intros α a,
      refl
    end,
  orelse_emp   :=
    begin
      intros α a,
      cases' a,
      { refl },
      { refl }
    end,
  orelse_assoc :=
    begin
      intros α a b c,
      cases' a,
      { refl },
      { refl }
    end,
  emp_bind     :=
    begin
      intros α β f,
      refl
    end,
  bind_emp     :=
    begin
      intros α β g,
      cases' g,
      { refl },
      { refl }
    end,
  .. option.lawful_monad }

@[simp] lemma option.some_bind {α β : Type} (a : α) (g : α → option β) :
  (option.some a >>= g) = g a :=
by refl

/- Let us enable some convenient pattern matching syntax, by instantiating
Lean's `monad_fail` type class. (Do not worry if you do not understand what
we are referring to.) -/

@[instance] def lawful_monad_with_orelse.monad_fail {m : Type → Type}
  [lawful_monad_with_orelse m] : monad_fail m :=
{ fail := λα msg, lawful_monad_with_orelse.emp }

/- Now we can write definitions such as the following: -/

def first_of_three {m : Type → Type} [lawful_monad_with_orelse m]
  (c : m (list ℕ)) : m ℕ :=
do
  [n, _, _] ← c,
  pure n

#eval first_of_three (option.some [1])
#eval first_of_three (option.some [1, 2, 3])
#eval first_of_three (option.some [1, 2, 3, 4])

/- Using `lawful_monad_with_orelse` and the `monad_fail` syntax, we can give a
concise definition for the `sum_2_5_7` function seen in the lecture. -/

def sum_2_5_7₇ {m : Type → Type} [lawful_monad_with_orelse m]
  (c : m (list ℕ)) : m ℕ :=
do
  (_ :: n2 :: _ :: _ :: n5 :: _ :: n7 :: _) ← c,
  pure (n2 + n5 + n7)

/- 1.2. Now we are ready to define `faction σ` ("eff action"): a monad with an
internal state of type `σ` that can fail (unlike `action σ`).

We start with defining `faction σ α`, where `σ` is the type of the internal
state, and `α` is the type of the value stored in the monad. We use `option` to
model failure. This means we can also use the monadic behavior of `option` when
defining the monadic operations on `faction`.

Hints:

* Remember that `faction σ α` is an alias for a function type, so you can use
  pattern matching and `λs, …` to define values of type `faction σ α`.

* `faction` is very similar to `action` from the lecture's demo. You can look
  there for inspiration. -/

def faction (σ : Type) (α : Type) :=
σ → option (α × σ)

/- 1.3. Define the `get` and `set` function for `faction`, where `get` returns
the state passed along the state monad and `set s` changes the state to `s`. -/

def get {σ : Type} : faction σ σ
| s := option.some (s, s)

def set {σ : Type} (s : σ) : faction σ unit
| _ := option.some ((), s)

/- We set up the `>>=` syntax on `faction`: -/

def faction.bind {σ α β : Type} (f : faction σ α) (g : α → faction σ β) :
  faction σ β
| s := f s >>= (λas, g (prod.fst as) (prod.snd as))


@[instance] def faction.has_bind {σ : Type} : has_bind (faction σ) :=
{ bind := @faction.bind σ }

lemma faction.bind_apply {σ α β : Type} (f : faction σ α) (g : α → faction σ β)
    (s : σ) :
  (f >>= g) s = (f s >>= (λas, g (prod.fst as) (prod.snd as))) :=
by refl

/- 1.4. Define the monadic operator `pure` for `faction`, in such a way that it
will satisfy the monad laws. -/

def faction.pure {σ α : Type} (a : α) : faction σ α
| s := option.some (a, s)

/- We set up the syntax for `pure` on `faction`: -/

@[instance] def faction.has_pure {σ : Type} : has_pure (faction σ) :=
{ pure := @faction.pure σ }

lemma faction.pure_apply {σ α : Type} (a : α) (s : σ) :
  (pure a : faction σ α) s = option.some (a, s) :=
by refl

/- 1.3. Register `faction` as a monad.

Hints:

* The `funext` lemma is useful when you need to prove equality between two
  functions.

* `cases' f s` only works when `f s` appears in your goal, so you may need to
  unfold some constants before you can invoke `cases'`. -/

@[instance] def faction.lawful_monad {σ : Type} : lawful_monad (faction σ) :=
{ pure_bind  :=
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
      simp [faction.bind_apply, faction.pure_apply],
      apply lawful_monad.bind_pure
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      apply funext,
      intro s,
      simp [faction.bind_apply],
      cases' ma s,
      { refl },
      { cases' val,
        refl }
    end,
  .. faction.has_bind,
  .. faction.has_pure }


/- ## Question 2: Kleisli Operator

The Kleisli operator `>=>` (not to be confused with `>>=`) is useful for
pipelining monadic operations. Note that `λa, f a >>= g` is to be parsed as
`λa, (f a >>= g)`, not as `(λa, f a) >>= g`. -/

def kleisli {m : Type → Type} [lawful_monad m] {α β γ : Type} (f : α → m β)
  (g : β → m γ) : α → m γ :=
λa, f a >>= g

infixr ` >=> ` : 90 := kleisli

/- 2.1. Prove that `pure` is a left and right unit for the Kleisli operator. -/

lemma pure_kleisli {m : Type → Type} [lawful_monad m] {α β : Type}
    (f : α → m β) :
  (pure >=> f) = f :=
begin
  apply funext,
  intro a,
  exact lawful_monad.pure_bind a f
end

lemma kleisli_pure {m : Type → Type} [lawful_monad m] {α β : Type}
    (f : α → m β) :
  (f >=> pure) = f :=
begin
  apply funext,
  intro a,
  exact lawful_monad.bind_pure (f a)
end

/- 2.2. Prove associativity of the Kleisli operator. -/

lemma kleisli_assoc {m : Type → Type} [lawful_monad m] {α β γ δ : Type}
    (f : α → m β) (g : β → m γ) (h : γ → m δ) :
  ((f >=> g) >=> h) = (f >=> (g >=> h)) :=
begin
  apply funext,
  intro a,
  exact lawful_monad.bind_assoc g h (f a)
end

end LoVe
