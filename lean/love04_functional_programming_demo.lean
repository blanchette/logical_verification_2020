import .lovelib


/- # LoVe Demo 4: Functional Programming

We take a closer look at the basics of typed functional programming: inductive
types, proofs by induction, recursive functions, pattern matching, structures
(records), and type classes. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Inductive Types

Recall the definition of type `nat` (= `ℕ`): -/

#print nat

/- Mottos:

* **No junk**: The type contains no values beyond those expressible using the
  constructors.

* **No confusion**: Values built in a different ways are different.

For `nat` (= `ℕ`):

* "No junk" means that there are no special values, say, `–1` or `ε`, that
  cannot be expressed using a finite combination of `zero` and `succ`.

* "No confusion" is what ensures that `zero` ≠ `succ x`.

In addition, inductive types are always finite. `succ (succ (succ …))` is not a
value.


## Structural Induction

__Structural induction__ is a generalization of mathematical induction to
inductive types. To prove a property `P[n]` for all natural numbers `n`, it
suffices to prove the base case

    `P[0]`

and the induction step

    `∀k, P[k] → P[k + 1]`

For lists, the base case is

    `P[[]]`

and the induction step is

    `∀y ys, P[ys] → P[y :: ys]`

In general, there is one subgoal per constructor, and induction hypotheses are
available for all constructor arguments of the type we are doing the induction
on. -/

lemma nat.succ_neq_self (n : ℕ) :
  nat.succ n ≠ n :=
begin
  induction' n,
  { simp },
  { simp [ih] }
end

/- The `case` tactic can be used to supply custom names, and potentially
reorder the cases. -/

lemma nat.succ_neq_self₂ (n : ℕ) :
  nat.succ n ≠ n :=
begin
  induction' n,
  case succ : m IH {
    simp [IH] },
  case zero {
    simp }
end


/- ## Structural Recursion

__Structural recursion__ is a form of recursion that allows us to peel off
one or more constructors from the value on which we recurse. Such functions are
guaranteed to call themselves only finitely many times before the recursion
stops. This is a prerequisite for establishing that the function terminates. -/

def fact : ℕ → ℕ
| 0       := 1
| (n + 1) := (n + 1) * fact n

def fact₂ : ℕ → ℕ
| 0       := 1
| 1       := 1
| (n + 1) := (n + 1) * fact₂ n

/- For structurally recursive functions, Lean can automatically prove
termination. For more general recursive schemes, the termination check may fail.
Sometimes it does so for a good reason, as in the following example: -/

-- fails
def illegal : ℕ → ℕ
| n := illegal n + 1

constant immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
  immoral n = immoral n + 1

lemma proof_of_false :
  false :=
have immoral 0 = immoral 0 + 1 :=
  immoral_eq 0,
have immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 :=
  by cc,
have 0 = 1 :=
  by simp [*] at *,
show false, from
  by cc


/- ## Pattern Matching Expressions

    `match` _term₁_, …, _termM_ `with`
    | _pattern₁₁_, …, _pattern₁M_ := _result₁_
        ⋮
    | _patternN₁_, …, _patternNM_ := _resultN_
    `end`

`match` allows nonrecursive pattern matching within terms.

In contrast to pattern matching after `lemma` or `def`, the patterns are
separated by commas, so parentheses are optional. -/

def bcount {α : Type} (p : α → bool) : list α → ℕ
| []        := 0
| (x :: xs) :=
  match p x with
  | tt := bcount xs + 1
  | ff := bcount xs
  end

def min (a b : ℕ) : ℕ :=
if a ≤ b then a else b


/- ## Structures

Lean provides a convenient syntax for defining records, or structures. These are
essentially nonrecursive, single-constructor inductive types. -/

structure rgb :=
(red green blue : ℕ)

#check rgb.mk
#check rgb.red
#check rgb.green
#check rgb.blue

namespace rgb_as_inductive

inductive rgb : Type
| mk : ℕ → ℕ → ℕ → rgb

def rgb.red : rgb → ℕ
| (rgb.mk r _ _) := r

def rgb.green : rgb → ℕ
| (rgb.mk _ g _) := g

def rgb.blue : rgb → ℕ
| (rgb.mk _ _ b) := b

end rgb_as_inductive

structure rgba extends rgb :=
(alpha : ℕ)

#print rgba

def pure_red : rgb :=
{ red   := 0xff,
  green := 0x00,
  blue  := 0x00 }

def semitransparent_red : rgba :=
{ alpha := 0x7f,
  ..pure_red }

#print pure_red
#print semitransparent_red

def shuffle (c : rgb) : rgb :=
{ red   := rgb.green c,
  green := rgb.blue c,
  blue  := rgb.red c }

/- `cases'` performs a case distinction on the specified term. This gives rise
to as many subgoals as there are constructors in the definition of the term's
type. The tactic behaves the same as `induction'` except that it does not
produce induction hypotheses. -/

lemma shuffle_shuffle_shuffle (c : rgb) :
  shuffle (shuffle (shuffle c)) = c :=
begin
  cases' c,
  refl
end

lemma shuffle_shuffle_shuffle₂ (c : rgb) :
  shuffle (shuffle (shuffle c)) = c :=
match c with
| rgb.mk r g b := eq.refl _
end


/- ## Type Classes

A __type class__ is a structure type combining abstract constants and their
properties. A type can be declared an instance of a type class by providing
concrete definitions for the constants and proving that the properties hold.
Based on the type, Lean retrieves the relevant instance. -/

#print inhabited

@[instance] def nat.inhabited : inhabited ℕ :=
{ default := 0 }

@[instance] def list.inhabited {α : Type} :
  inhabited (list α) :=
{ default := [] }

#eval inhabited.default ℕ          -- result: 0
#eval inhabited.default (list ℤ)   -- result: []

def head {α : Type} [inhabited α] : list α → α
| []       := inhabited.default α
| (x :: _) := x

lemma head_head {α : Type} [inhabited α] (xs : list α) :
  head [head xs] = head xs :=
begin
  cases' xs,
  { refl },
  { refl }
end

#eval head ([] : list ℕ)   -- result: 0

#check list.head

@[instance] def fun.inhabited {α β : Type} [inhabited β] :
  inhabited (α → β) :=
{ default := λa : α, inhabited.default β }

inductive empty : Type

@[instance] def fun_empty.inhabited {β : Type} :
  inhabited (empty → β) :=
{ default := λa : empty, match a with end }

@[instance] def prod.inhabited {α β : Type}
    [inhabited α] [inhabited β] :
  inhabited (α × β) :=
{ default := (inhabited.default α, inhabited.default β) }

/- Here are other type classes without properties: -/

#check has_zero
#check has_neg
#check has_add
#check has_one
#check has_inv
#check has_mul

#check (1 : ℕ)
#check (1 : ℤ)
#check (1 : ℝ)

/- We encountered these type classes in lecture 2: -/

#print is_commutative
#print is_associative


/- ## Lists

`list` is an inductive polymorphic type constructed from `nil` and `cons`: -/

#print list

/- `cases'` can also be used on a hypothesis of the form `l = r`. It matches `r`
against `l` and replaces all occurrences of the variables occurring in `r` with
the corresponding terms in `l` everywhere in the goal. -/

lemma injection_example {α : Type} (x y : α) (xs ys : list α)
    (h : list.cons x xs = list.cons y ys) :
  x = y ∧ xs = ys :=
begin
  cases' h,
  cc
end

/- If `r` fails to match `l`, no subgoals emerge; the proof is complete. -/

lemma distinctness_example {α : Type} (y : α) (ys : list α)
    (h : [] = y :: ys) :
  false :=
by cases' h

def map {α β : Type} (f : α → β) : list α → list β
| []        := []
| (x :: xs) := f x :: map xs

def map₂ {α β : Type} : (α → β) → list α → list β
| _ []        := []
| f (x :: xs) := f x :: map₂ f xs

#check list.map

lemma map_ident {α : Type} (xs : list α) :
  map (λx, x) xs = xs :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end

lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (xs : list α) :
  map g (map f xs) = map (λx, g (f x)) xs :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end

lemma map_append {α β : Type} (f : α → β) (xs ys : list α) :
  map f (xs ++ ys) = map f xs ++ map f ys :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end

def tail {α : Type} : list α → list α
| []        := []
| (_ :: xs) := xs

#check list.tail

def head_opt {α : Type} : list α → option α
| []       := option.none
| (x :: _) := option.some x

def head_le {α : Type} : ∀xs : list α, xs ≠ [] → α
| []       hxs := by cc
| (x :: _) _   := x

#eval head_opt [3, 1, 4]
#eval head_le [3, 1, 4] (by simp)
-- fails
#eval head_le ([] : list ℕ) sorry

def zip {α β : Type} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| []        _         := []
| (_ :: _)  []        := []

#check list.zip

def length {α : Type} : list α → ℕ
| []        := 0
| (x :: xs) := length xs + 1

#check list.length

/- `cases'` can also be used to perform a case distinction on a proposition, in
conjunction with `classical.em`. Two cases emerge: one in which the proposition
is true and one in which it is false. -/

#check classical.em

lemma min_add_add (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
begin
  cases' classical.em (m ≤ n),
  case inl {
    simp [min, h] },
  case inr {
    simp [min, h] }
end

lemma min_add_add₂ (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
match classical.em (m ≤ n) with
| or.inl h := by simp [min, h]
| or.inr h := by simp [min, h]
end

lemma min_add_add₃ (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
if h : m ≤ n then
  by simp [min, h]
else
  by simp [min, h]

lemma length_zip {α β : Type} (xs : list α) (ys : list β) :
  length (zip xs ys) = min (length xs) (length ys) :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : x xs' {
    cases' ys,
    case nil {
      refl },
    case cons : y ys' {
      simp [zip, length, ih ys', min_add_add] } }
end

lemma map_zip {α α' β β' : Type} (f : α → α') (g : β → β') :
  ∀xs ys,
    map (λab : α × β, (f (prod.fst ab), g (prod.snd ab)))
      (zip xs ys) =
    zip (map f xs) (map g ys)
| (x :: xs) (y :: ys) := by simp [zip, map, map_zip xs ys]
| []        _         := by refl
| (_ :: _)  []        := by refl


/- ## Binary Trees

Inductive types with constructors taking several recursive arguments define
tree-like objects. __Binary trees__ have nodes with at most two children. -/

inductive btree (α : Type) : Type
| empty {} : btree
| node     : α → btree → btree → btree

/- The type `aexp` of arithmetic expressions was also an example of a tree data
structure.

The nodes of a tree, whether inner nodes or leaf nodes, often carry labels or
other annotations.

Inductive trees contain no infinite branches, not even cycles. This is less
expressive than pointer- or reference-based data structures (in imperative
languages) but easier to reason about.

Recursive definitions (and proofs by induction) work roughly as for lists, but
we may need to recurse (or invoke the induction hypothesis) on several child
nodes. -/

def mirror {α : Type} : btree α → btree α
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node a (mirror r) (mirror l)

lemma mirror_mirror {α : Type} (t : btree α) :
  mirror (mirror t) = t :=
begin
  induction' t,
  case empty {
    refl },
  case node : a l r ih_l ih_r {
    simp [mirror, ih_l, ih_r] }
end

lemma mirror_mirror₂ {α : Type} :
  ∀t : btree α, mirror (mirror t) = t
| btree.empty        := by refl
| (btree.node a l r) :=
  calc  mirror (mirror (btree.node a l r))
      = mirror (btree.node a (mirror r) (mirror l)) :
    by refl
  ... = btree.node a (mirror (mirror l)) (mirror (mirror r)) :
    by refl
  ... = btree.node a l (mirror (mirror r)) :
    by rw mirror_mirror₂ l
  ... = btree.node a l r :
    by rw mirror_mirror₂ r

lemma mirror_eq_empty_iff {α : Type} :
  ∀t : btree α, mirror t = btree.empty ↔ t = btree.empty
| btree.empty        := by refl
| (btree.node _ _ _) := by simp [mirror]


/- ## Dependent Inductive Types (**optional**) -/

#check vector

inductive vec (α : Type) : ℕ → Type
| nil {}                           : vec 0
| cons (a : α) {n : ℕ} (v : vec n) : vec (n + 1)

#check vec.nil
#check vec.cons

def list_of_vec {α : Type} : ∀{n : ℕ}, vec α n → list α
| _ vec.nil        := []
| _ (vec.cons a v) := a :: list_of_vec v

def vec_of_list {α : Type} :
  ∀xs : list α, vec α (list.length xs)
| []        := vec.nil
| (x :: xs) := vec.cons x (vec_of_list xs)

lemma length_list_of_vec {α : Type} :
  ∀{n : ℕ} (v : vec α n), list.length (list_of_vec v) = n
| _ vec.nil        := by refl
| _ (vec.cons a v) :=
  by simp [list_of_vec, length_list_of_vec v]

end LoVe
