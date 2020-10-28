import .love03_forward_proofs_demo
import .love04_functional_programming_demo


/- # LoVe Demo 5: Inductive Predicates

__Inductive predicates__, or inductively defined propositions, are a convenient
way to specify functions of type `⋯ → Prop`. They are reminiscent of formal
systems and of the Horn clauses of Prolog, the logic programming language par
excellence.

A possible view of Lean:

    Lean = functional programming + logic programming + more logic -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Introductory Examples

### Even Numbers

Mathematicians often define sets as the smallest that meets some criteria. For
example:

    The set `E` of even natural numbers is defined as the smallest set closed
    under the following rules: (1) `0 ∈ E` and (2) for every `k ∈ ℕ`, if
    `k ∈ E`, then `k + 2 ∈ E`.

In Lean, we can define the corresponding "is even" predicate as follows: -/

inductive even : ℕ → Prop
| zero    : even 0
| add_two : ∀k : ℕ, even k → even (k + 2)

/- This should look familiar. We have used the same syntax, except with `Type`
instead of `Prop`, for inductive types.

The above command introduces a new unary predicate `even` as well as two
constructors, `even.zero` and `even.add_two`, which can be used to build proof
terms. Thanks to the "no junk" guarantee of inductive definitions, `even.zero`
and `even.add_two` are the only two ways to construct proofs of `even`.

By the Curry–Howard correspondence, `even` can be seen as an inductive type, the
values being the proof terms. -/

lemma even_4 :
  even 4 :=
have even_0 : even 0 :=
  even.zero,
have even_2 : even 2 :=
  even.add_two _ even_0,
show even 4, from
  even.add_two _ even_2

/- Why cannot we simply define `even` recursively? Indeed, why not? -/

def even₂ : ℕ → bool
| 0       := tt
| 1       := ff
| (k + 2) := even₂ k

/- There are advantages and disadvantages to both styles.

The recursive version requires us to specify a false case (1), and it requires
us to worry about termination. On the other hand, because it is computational,
it works well with `refl`, `simp`, `#reduce`, and `#eval`.

The inductive version is often considered more abstract and elegant. Each rule
is stated independently of the others.

Yet another way to define `even` is as a nonrecursive definition: -/

def even₃ (k : ℕ) : bool :=
k % 2 = 0

/- Mathematicians would probably find this the most satisfactory definition.
But the inductive version is a convenient, intuitive example that is typical of
many realistic inductive definitions.


### Tennis Games

Transition systems consists of transition rules, which together specify a
binary predicate connecting a "before" and an "after" state. As a simple
specimen of a transition system, we consider the possible transitions, in a game
of tennis, starting from 0–0. -/

inductive score : Type
| vs       : ℕ → ℕ → score
| adv_srv  : score
| adv_rcv  : score
| game_srv : score
| game_rcv : score

infixr ` – ` : 10 := score.vs

inductive step : score → score → Prop
| srv_0_15    : ∀n, step (0–n) (15–n)
| srv_15_30   : ∀n, step (15–n) (30–n)
| srv_30_40   : ∀n, step (30–n) (40–n)
| srv_40_game : ∀n, n < 40 → step (40–n) score.game_srv
| srv_40_adv  : step (40–40) score.adv_srv
| srv_adv_40  : step score.adv_srv (40–40)
| rcv_0_15    : ∀n, step (n–0) (n–15)
| rcv_15_30   : ∀n, step (n–15) (n–30)
| rcv_30_40   : ∀n, step (n–30) (n–40)
| rcv_40_game : ∀n, n < 40 → step (n–40) score.game_rcv
| rcv_40_adv  : step (40–40) score.adv_rcv
| rcv_adv_40  : step score.adv_rcv (40–40)

infixr ` ⇒ ` := step

/- We can ask, and formally answer, questions such as: Is this transition
system confluent? Does it always terminate? Can the score 65–15 be reached from
0–0?


### Reflexive Transitive Closure

Our last introductory example is the reflexive transitive closure of a
relation `r`, modeled as a binary predicate `star r`. -/

inductive star {α : Type} (r : α → α → Prop) : α → α → Prop
| base (a b : α)    : r a b → star a b
| refl (a : α)      : star a a
| trans (a b c : α) : star a b → star b c → star a c

/- The first rule embeds `r` into `star r`. The second rule achieves the
reflexive closure. The third rule achieves the transitive closure.

The definition is truly elegant. If you doubt this, try implementing `star` as a
recursive function: -/

def star₂ {α : Type} (r : α → α → Prop) : α → α → Prop :=
sorry


/- ### A Nonexample

Not all inductive definitions admit a least solution. -/

-- fails
inductive illegal₂ : Prop
| intro : ¬ illegal₂ → illegal₂


/- ## Logical Symbols

The truth values `false` and `true`, the connectives `∧` and `∨`, the
`∃`-quantifier, and the equality predicate `=` are all defined as inductive
propositions or predicates. In contrast, `∀` (= `Π`) and `→` are built into
the logic.

Syntactic sugar:

    `∃x : α, p` := `Exists (λx : α, p)`
    `x = y`     := `eq x y` -/

namespace logical_symbols

inductive and (a b : Prop) : Prop
| intro : a → b → and

inductive or (a b : Prop) : Prop
| intro_left  : a → or
| intro_right : b → or

inductive iff (a b : Prop) : Prop
| intro : (a → b) → (b → a) → iff

inductive Exists {α : Type} (p : α → Prop) : Prop
| intro : ∀a : α, p a → Exists

inductive true : Prop
| intro : true

inductive false : Prop

inductive eq {α : Type} : α → α → Prop
| refl : ∀a : α, eq a a

end logical_symbols

#print and
#print or
#print iff
#print Exists
#print true
#print false
#print eq


/- ## Rule Induction

Just as we can perform induction on a term, we can perform induction on a proof
term.

This is called __rule induction__, because the induction is on the introduction
rules (i.e., the constructors of the proof term). Thanks to the Curry–Howard
correspondence, this works as expected. -/

lemma mod_two_eq_zero_of_even (n : ℕ) (h : even n) :
  n % 2 = 0 :=
begin
  induction' h,
  case zero {
    refl },
  case add_two : k hk ih {
    simp [ih] }
end

lemma not_even_two_mul_add_one (n : ℕ) :
  ¬ even (2 * n + 1) :=
begin
  intro h,
  induction' h,
  apply ih (n - 1),
  cases' n,
  case zero {
    linarith },
  case succ {
    simp [nat.succ_eq_add_one] at *,
    linarith }
end

/- `linarith` proves goals involving linear arithmetic equalities or
inequalities. "Linear" means it works only with `+` and `-`, not `*` and `/`
(but multiplication by a constant is supported). -/

lemma linarith_example (i : ℤ) (hi : i > 5) :
  2 * i + 3 > 11 :=
by linarith

lemma star_star_iff_star {α : Type} (r : α → α → Prop)
    (a b : α) :
  star (star r) a b ↔ star r a b :=
begin
  apply iff.intro,
  { intro h,
    induction' h,
    case base : a b hab {
      exact hab },
    case refl : a {
      apply star.refl },
    case trans : a b c hab hbc ihab ihbc {
      apply star.trans a b,
      { exact ihab },
      { exact ihbc } } },
  { intro h,
    apply star.base,
    exact h }
end

@[simp] lemma star_star_eq_star {α : Type}
    (r : α → α → Prop) :
  star (star r) = star r :=
begin
  apply funext,
  intro a,
  apply funext,
  intro b,
  apply propext,
  apply star_star_iff_star
end

#check funext
#check propext


/- ## Elimination

Given an inductive predicate `p`, its introduction rules typically have the form
`∀…, ⋯ → p …` and can be used to prove goals of the form `⊢ p …`.

Elimination works the other way around: It extracts information from a lemma or
hypothesis of the form `p …`. Elimination takes various forms: pattern matching,
the `cases'` and `induction'` tactics, and custom elimination rules (e.g.,
`and.elim_left`).

* `cases'` works like `induction'` but without induction hypothesis.

* `match` is available as well, but it corresponds to dependently typed pattern
  matching (cf. `vector` in lecture 4).

Now we can finally analyze how `cases' h`, where `h : l = r`, and how
`cases' classical.em h` work. -/

#print eq

lemma cases_eq_example {α : Type} (l r : α) (h : l = r)
    (p : α → α → Prop) :
  p l r :=
begin
  cases' h,
  sorry
end

#check classical.em
#print or

lemma cases_classical_em_example {α : Type} (a : α)
    (p q : α → Prop) :
  q a :=
begin
  have h : p a ∨ ¬ p a :=
    classical.em (p a),
  cases' h,
  case inl {
    sorry },
  case inr {
    sorry }
end

/- Often it is convenient to rewrite concrete terms of the form `p (c …)`,
where `c` is typically a constructor. We can state and prove an
__inversion rule__ to support such eliminative reasoning.

Typical inversion rule:

    `∀x y, p (c x y) → (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)`

It can be useful to combine introduction and elimination into a single lemma,
which can be used for rewriting both the hypotheses and conclusions of goals:

    `∀x y, p (c x y) ↔ (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)` -/

lemma even_iff (n : ℕ) :
  even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ even m) :=
begin
  apply iff.intro,
  { intro hn,
    cases' hn,
    case zero {
      simp },
    case add_two : k hk {
      apply or.intro_right,
      apply exists.intro k,
      simp [hk] } },
  { intro hor,
    cases' hor,
    case inl : heq {
      simp [heq, even.zero] },
    case inr : hex {
      cases' hex with k hand,
      cases' hand with heq hk,
      simp [heq, even.add_two _ hk] } }
end

lemma even_iff₂ (n : ℕ) :
  even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ even m) :=
iff.intro
  (assume hn : even n,
   match n, hn with
   | _, even.zero         :=
     show 0 = 0 ∨ _, from
       by simp
   | _, even.add_two k hk :=
     show _ ∨ (∃m, k + 2 = m + 2 ∧ even m), from
       or.intro_right _ (exists.intro k (by simp [*]))
   end)
  (assume hor : n = 0 ∨ (∃m, n = m + 2 ∧ even m),
   match hor with
   | or.intro_left _ heq :=
     show even n, from
       by simp [heq, even.zero]
   | or.intro_right _ hex :=
     match hex with
     | Exists.intro m hand :=
       match hand with
       | and.intro heq hm :=
         show even n, from
           by simp [heq, even.add_two _ hm]
       end
     end
   end)


/- ## Further Examples

### Sorted Lists -/

inductive sorted : list ℕ → Prop
| nil : sorted []
| single {x : ℕ} : sorted [x]
| two_or_more {x y : ℕ} {zs : list ℕ} (hle : x ≤ y)
    (hsorted : sorted (y :: zs)) :
  sorted (x :: y :: zs)

lemma sorted_nil :
  sorted [] :=
sorted.nil

lemma sorted_2 :
  sorted [2] :=
sorted.single

lemma sorted_3_5 :
  sorted [3, 5] :=
begin
  apply sorted.two_or_more,
  { linarith },
  { exact sorted.single }
end

lemma sorted_3_5₂ :
  sorted [3, 5] :=
sorted.two_or_more (by linarith) sorted.single

lemma sorted_7_9_9_11 :
  sorted [7, 9, 9, 11] :=
sorted.two_or_more (by linarith)
  (sorted.two_or_more (by linarith)
     (sorted.two_or_more (by linarith)
        sorted.single))

lemma not_sorted_17_13 :
  ¬ sorted [17, 13] :=
begin
  intro h,
  cases' h,
  linarith
end


/- ### Palindromes -/

inductive palindrome {α : Type} : list α → Prop
| nil : palindrome []
| single (x : α) : palindrome [x]
| sandwich (x : α) (xs : list α) (hxs : palindrome xs) :
  palindrome ([x] ++ xs ++ [x])

-- fails
def palindrome₂ {α : Type} : list α → Prop
| []                 := true
| [_]                := true
| ([x] ++ xs ++ [x]) := palindrome₂ xs
| _                  := false

lemma palindrome_aa {α : Type} (a : α) :
  palindrome [a, a] :=
palindrome.sandwich a _ palindrome.nil

lemma palindrome_aba {α : Type} (a b : α) :
  palindrome [a, b, a] :=
palindrome.sandwich a _ (palindrome.single b)

lemma reverse_palindrome {α : Type} (xs : list α)
    (hxs : palindrome xs) :
  palindrome (reverse xs) :=
begin
  induction' hxs,
  case nil {
    exact palindrome.nil },
  case single {
    exact palindrome.single x },
  case sandwich {
    simp [reverse, reverse_append],
    exact palindrome.sandwich _ _ ih }
end


/- ### Full Binary Trees -/

#check btree

inductive is_full {α : Type} : btree α → Prop
| empty : is_full btree.empty
| node (a : α) (l r : btree α)
    (hl : is_full l) (hr : is_full r)
    (hiff : l = btree.empty ↔ r = btree.empty) :
  is_full (btree.node a l r)

lemma is_full_singleton {α : Type} (a : α) :
  is_full (btree.node a btree.empty btree.empty) :=
begin
  apply is_full.node,
  { exact is_full.empty },
  { exact is_full.empty },
  { refl }
end

lemma is_full_mirror {α : Type} (t : btree α)
    (ht : is_full t) :
  is_full (mirror t) :=
begin
  induction' ht,
  case empty {
    exact is_full.empty },
  case node : a l r hl hr hiff ih_l ih_r {
    rw mirror,
    apply is_full.node,
    { exact ih_r },
    { exact ih_l },
    { simp [mirror_eq_empty_iff, *] } }
end

lemma is_full_mirror₂ {α : Type} :
  ∀t : btree α, is_full t → is_full (mirror t)
| btree.empty        :=
  begin
    intro ht,
    exact ht
  end
| (btree.node a l r) :=
  begin
    intro ht,
    cases ht with _ _ _ hl hr hiff,
    rw mirror,
    apply is_full.node,
    { exact is_full_mirror₂ _ hr },
    { apply is_full_mirror₂ _ hl },
    { simp [mirror_eq_empty_iff, *] }
  end


/- ### First-Order Terms -/

inductive term (α β : Type) : Type
| var {} : β → term
| fn     : α → list term → term

inductive well_formed {α β : Type} (arity : α → ℕ) :
  term α β → Prop
| var (x : β) : well_formed (term.var x)
| fn (f : α) (ts : list (term α β))
    (hargs : ∀t ∈ ts, well_formed t)
    (hlen : list.length ts = arity f) :
  well_formed (term.fn f ts)

inductive variable_free {α β : Type} : term α β → Prop
| fn (f : α) (ts : list (term α β))
    (hargs : ∀t ∈ ts, variable_free t) :
  variable_free (term.fn f ts)

end LoVe
