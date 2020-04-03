import .love05_inductive_predicates_demo


/-! # LoVe Demo 11: Logical Foundations of Mathematics

We dive deeper into the logical foundations of Lean. Most of the features
described here are especially relevant for defining mathematical objects and
proving theorems about them. -/


set_option pp.beta true

namespace LoVe


/-! ## Type Universes

Not only terms have a type, but also types have a type. For example, by the
Curry-Howard correspondence:

    `@and.intro : ∀a b, a → b → a ∧ b`

Moreover:

    `∀a b, a → b → a ∧ b : Prop`

Now, what is the type of `Prop`? `Prop` has the same type as virtually all other
types we have constructed so far:

    `Prop : Type`

What is the type of `Type`? The typing `Type : Type` would lead to a
contradiction, called **Girard's paradox**, resembling Russel's paradox.
Instead:

    `Type   : Type 1`
    `Type 1 : Type 2`
    `Type 2 : Type 3`
    ⋮

Aliases:

    `Type`   := `Type 0`
    `Prop`   := `Sort 0`
    `Type u` := `Sort (u + 1)`

The types of types (`Sort u`, `Type u`, and `Prop`) are called (__type__)
__universes__. The `u` in `Sort u` is a __universe level__.

The hierarchy is captured by the following typing judgment:

    ————————————————————————— Sort
    C ⊢ Sort u : Sort (u + 1) -/

#check @and.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe variables u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type*


/-! ## The Peculiarities of Prop

`Prop` is different from the other type universes in many respects.


### Impredicativity

The function type `σ → τ` is put into the larger one of the type universes that
`σ` and `τ` live in:

    C ⊢ σ : Type u    C ⊢ τ : Type v
    ————————————————————————————————— Arrow-Type
    C ⊢ σ → τ : Type (max u v)

For dependent types, this generalizes to

    C ⊢ σ : Type u    C, x : σ ⊢ τ[x] : Type v
    ——————————————————————————————————————————— Forall-Type
    C ⊢ (∀x : σ, τ[x]) : Type (max u v)

This behavior of the universes `Type v` is called __predicativity__.

To force expressions such as `∀a : Prop, a → a` to be of type `Prop` anyway, we
need a special typing rule for `Prop`:

    C ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    —————————————————————————————————————— Forall-Prop
    C ⊢ (∀x : σ, τ[x]) : Prop

This behavior of `Prop` is called __impredicativity__.

The rules `Forall-Type` and `Forall-Prop` can be generalized into a single rule:

    C ⊢ σ : Sort u    C, x : σ ⊢ τ[x] : Sort v
    ——————————————————————————————————————————— Forall
    C ⊢ (∀x : σ, τ[x]) : Sort (imax u v)

where

    `imax u 0       = 0`
    `imax u (v + 1) = max u (v + 1)` -/

#check λ(α : Type u) (β : Type v), α → β
#check ∀a : Prop, a → a


/-! ### Proof Irrelevance

A second difference between `Prop` and `Type u` is __proof irrelevance__:

    `∀(a : Prop) (h₁ h₂ : a), h₁ = h₂`

This and makes reasoning about dependent types easier.

When viewing a proposition as a type and a proof as an element of that type,
proof irrelevance means that a proposition is either an empty type or has
exactly one inhabitant.

Proof irrelevance can be proved `by refl`.

An unfortunate consequence of proof irrelevance is that it prevents us from
performing rule induction by pattern matching. -/

#check proof_irrel

lemma proof_irrel {a : Prop} (h₁ h₂ : a) :
  h₁ = h₂ :=
by refl


/-! ### No Large Elimination

A further difference between `Prop` and `Type u` is that `Prop` does not allow
__large elimination__, meaning that it impossible to extract data from a proof
of a proposition.

This is necessary to allow proof irrelevance. -/

#check 0

-- fails
def unsquare (i : ℤ) (hsq : ∃j, i = j * j) : ℤ :=
match hsq with
| Exists.intro j _ := j
end

/-! If the above were accepted, we could derive `false` as follows.

Let

    `hsq₁` := `Exists.intro 3 dec_trivial`
    `hsq₂` := `Exists.intro (-3) dec_trivial`

be two proofs of `∃j, (9 : ℤ) = j * j`. Then

    `unsquare 9 hsq₁ = 3`
    `unsquare 9 hsq₂ = -3`

However, by proof irrelevance, `hsq₁ = hsq₂`. Hence

    `unsquare 9 hsq₂ = 3`

Thus

    `3 = -3`

a contradiction.

As a compromise, Lean allows __small elimination__. It is called small
elimination because it eliminate only into `Prop`, whereas large elimination can
eliminate into an arbitrary large type universe `Sort u`. This means we can use
`match` to analyze the structure of a proof, extract existential witnesses, and
so on, as long as the `match` expression is itself a proof. We have seen several
examples of this in lecture 5.

As a further compromise, Lean allows large elimination for
__syntactic subsingletons__: types in `Prop` for which it can be established
syntactically that they have cardinality 0 or 1. These are propositions such as
`false` and `a ∧ b` that can be proved in at most one way.


## The Axiom of Choice

Lean's logic includes the axiom of choice, which makes it possible to obtain an
arbitrary element from any nonempty type.

Consider Lean's `nonempty` inductive predicate: -/

#print nonempty

/-! The predicate states that `α` has at least one element.

To prove `nonempty α`, we must provide an `α` value to `nonempty.intro`: -/

lemma nat.nonempty :
  nonempty ℕ :=
nonempty.intro 0

/-! Since `nonempty` lives in `Prop`, large elimination is not available, and
thus we cannot extract the element that was used from a proof of `nonempty α`.

The axiom of choice allows us to obtain some element of type `α` if we can show
`nonempty α`: -/

#print classical.choice

/-! It will just give us an arbitrary element of `α`; we have no way of knowing
whether this is the element that was used to prove `nonempty α`.

The constant `classical.choice` is noncomputable, one of the reasons why some
logicians prefer to work without this axiom. -/

#eval classical.choice nat.nonempty     -- fails
#reduce classical.choice nat.nonempty   -- result: classical.choice _

/-! The axiom of choice is only an axiom in Lean's core library, giving users
the freedom to work with or without it.

Definitions using it must be marked as `noncomputable`: -/

noncomputable def arbitrary_nat : ℕ :=
classical.choice nat.nonempty

/-! The following tools rely on choice.


### Law of Excluded Middle -/

#check classical.em -- excluded middle
#check classical.by_contradiction


/-! ### Hilbert Choice -/

#print classical.some
#print classical.some_spec

#check λ(p : ℕ → Prop) (h : ∃n : ℕ, p n), classical.some h
#check λ(p : ℕ → Prop) (h : ∃n : ℕ, p n), classical.some_spec h


/-! ### Set-Theoretic Axiom of Choice -/

#print classical.axiom_of_choice


/-! ## Subtypes

Subtyping is a mechanism to create new types from existing ones.

Given a predicate on the elements of the base type, the __subtype__ contains
only those elements of the base type that fulfill this property. More precisely,
the subtype contains element–proof pairs that combine an element of the base
type and a proof that it fulfills the property.

Subtyping is useful for those types that cannot be defined as an inductive
type. For example, any attempt at defining the type of finite sets along the
following lines is doomed to fail: -/

inductive finset (α : Type) : Type
| empty  : finset
| insert : α → finset → finset

/-! Given a base type and a property, the subtype has the syntax

    `{` _variable_ `:` _base-type_ `//` _property-applied-to-variable_ `}`

Example:

    `{i : ℕ // i ≤ n}`

Alias:

    `{x : τ // P[x]}` := `@subtype τ (λx, P[x])`


### First Example: Full Binary Trees -/

#check btree
#check is_full
#check mirror
#check is_full_mirror
#check mirror_mirror

def full_btree (α : Type) : Type :=
{t : btree α // is_full t}

#print subtype
#check subtype.mk

/-! To define elements of `full_btree`, we must provide a `btree` and a proof
that it is full: -/

def empty_full_btree : full_btree ℕ :=
subtype.mk btree.empty is_full.empty

def full_btree_6 : full_btree ℕ :=
subtype.mk (btree.node 6 btree.empty btree.empty)
  begin
    apply is_full.node,
    apply is_full.empty,
    apply is_full.empty,
    refl
  end

#reduce subtype.val full_btree_6
#check subtype.property full_btree_6

/-! We can lift existing operations on `btree` to `full_btree`: -/

def full_btree.mirror {α : Type} (t : full_btree α) :
  full_btree α :=
subtype.mk (mirror (subtype.val t))
  begin
    apply is_full_mirror,
    apply subtype.property t
  end

#reduce subtype.val (full_btree.mirror full_btree_6)

/-! And of course we can prove lemmas about the lifted operations: -/

lemma full_btree.mirror_mirror {α : Type} (t : full_btree α) :
  (full_btree.mirror (full_btree.mirror t)) = t :=
begin
  apply subtype.eq,
  simp [full_btree.mirror],
  apply mirror_mirror
end

#check subtype.eq


/-! ### Second Example: Vectors -/

#check vector

def vector (α : Type) (n : ℕ) : Type :=
{xs : list α // list.length xs = n}

def vector_123 : vector ℤ 3 :=
subtype.mk [1, 2, 3] (by refl)

def vector.neg {n : ℕ} (v : vector ℤ n) : vector ℤ n :=
subtype.mk (list.map int.neg (subtype.val v))
  begin
    rewrite list.length_map,
    exact subtype.property v
  end

lemma vector.neg_neg (n : ℕ) (v : vector ℤ n) :
  vector.neg (vector.neg v) = v :=
begin
  apply subtype.eq,
  simp [vector.neg]
end

#check finset


/-! ## Quotient Types

Quotients are a powerful construction in mathematics used to construct `ℤ`, `ℚ`,
`ℝ`, and many other types.

Like subtyping, quotienting constructs a new type from an existing type. Unlike
a subtype, a quotient type contains all of the elements of the base type, but
some elements that were different in the base type are considered equal in the
quotient type. In mathematical terms, the quotient type is isomorphic to a
partition of the base type.

To define a quotient type, we need to provide a type that it is derived from and
a equivalence relation on it that determines which elements are considered
equal. -/

#check quotient
#print setoid

#check quotient.mk
#check quotient.sound
#check quotient.exact

#check quotient.lift
#check quotient.lift₂
#check quotient.induction_on


/-! ## First Example: Integers

Let us build the integers `ℤ` as a quotient over pairs of natural numbers
`ℕ × ℕ`.

A pair `(p, n)` of natural numbers represents the integer `p - n`. Nonnegative
integers `p` can be represented by `(p, 0)`. Negative integers `-n` can be
represented by `(0, n)`. However, many representations of the same integer are
possible; e.g., `(7, 0)`, `(8, 1)`, `(9, 2)`, and `(10, 3)` all represent the
integer `7`.

Which equivalence relation can we use?

We want two pairs `(p₁, n₁)` and `(p₂, n₂)` to be equal if `p₁ - n₁ = p₂ - n₂`.
However, this does not work because subtraction on `ℕ` is ill-behaved (e.g.,
`0 - 1 = 0`). Instead, we use `p₁ + n₂ = p₂ + n₁`. -/

@[instance] def int.rel : setoid (ℕ × ℕ) :=
{ r     :=
    λpn₁ pn₂ : ℕ × ℕ,
      prod.fst pn₁ + prod.snd pn₂ = prod.fst pn₂ + prod.snd pn₁,
  iseqv :=
    begin
      repeat { apply and.intro },
      { intro pn,
        refl },
      { intros pn₁ pn₂ h,
        rewrite h },
      { intros pn₁ pn₂ pn₃ h₁₂ h₂₃,
        apply @eq_of_add_eq_add_right _ _ _ (prod.snd pn₂),
        cc }
    end }

#print equivalence

lemma int.rel_iff (pn₁ pn₂ : ℕ × ℕ) :
  pn₁ ≈ pn₂ ↔
  prod.fst pn₁ + prod.snd pn₂ = prod.fst pn₂ + prod.snd pn₁ :=
by refl

def int : Type :=
quotient int.rel

def int.zero : int :=
⟦(0, 0)⟧

lemma int.zero_eq (m : ℕ) :
  int.zero = ⟦(m, m)⟧ :=
begin
  rewrite int.zero,
  apply quotient.sound,
  rewrite int.rel_iff,
  simp
end

def int.add : int → int → int :=
quotient.lift₂
  (λpn₁ pn₂ : ℕ × ℕ,
     ⟦(prod.fst pn₁ + prod.fst pn₂,
       prod.snd pn₁ + prod.snd pn₂)⟧)
  begin
    intros pn₁ pn₂ pn₁' pn₂' h₁ h₂,
    apply quotient.sound,
    rewrite int.rel_iff at *,
    linarith
  end

lemma int.add_eq (p₁ n₁ p₂ n₂ : ℕ) :
  int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ = ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
by refl

lemma int.add_zero (i : int) :
  int.add int.zero i = i :=
begin
  apply quotient.induction_on i,
  intro pn,
  rewrite int.zero,
  cases pn with p n,
  rewrite int.add_eq,
  apply quotient.sound,
  simp
end

/-! This definitional syntax would be nice: -/

-- fails
def int.add : int → int → int
| ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ := ⟦(p₁ + p₂, n₁ + n₂)⟧

/-! But it would be dangerous: -/

-- fails
def int.fst : int → ℕ
| ⟦(p, n)⟧ := p

/-! Using `int.fst`, we could derive `false`. First, we have

    `int.fst ⟦(0, 0)⟧ = 0`
    `int.fst ⟦(1, 1)⟧ = 1`

But since `⟦(0, 0)⟧ = ⟦(1, 1)⟧`, we get

    `0 = 1` -/


/-! ### Second Example: Unordered Pairs

__Unordered pairs__ are pairs for which no distinction is made between the first
and second components. They are usually written `{a, b}`.

We will introduce the type `upair` of unordered pairs as the quotient of pairs
`(a, b)` with respect to the relation "contains the same elements as". -/

@[instance] def upair.rel (α : Type) : setoid (α × α) :=
{ r     := λab₁ ab₂ : α × α,
    ({prod.fst ab₁, prod.snd ab₁} : set α) =
    ({prod.fst ab₂, prod.snd ab₂} : set α),
  iseqv := by repeat { apply and.intro }; finish }

-- downprioritizes `upair.rel` w.r.t. `int.rel`
attribute [instance, priority 999] upair.rel

lemma upair.rel_iff {α : Type} (ab₁ ab₂ : α × α) :
  ab₁ ≈ ab₂ ↔
  ({prod.fst ab₁, prod.snd ab₁} : set α) =
  ({prod.fst ab₂, prod.snd ab₂} : set α) :=
by refl

def upair (α : Type) : Type :=
quotient (upair.rel α)

def upair.mk {α : Type} (a b : α) : upair α :=
⟦(a, b)⟧

/-! It is easy to prove that the `upair.mk` constructor is symmetric: -/

lemma upair.mk_symm {α : Type} (a b : α) :
  upair.mk a b = upair.mk b a :=
begin
  unfold upair.mk,
  apply quotient.sound,
  rewrite upair.rel_iff,
  apply set.insert_comm
end

/-! Another representation of unordered pairs is as sets of cardinality 1 or 2.
The following operation converts `upair` to that representation: -/

def set_of_upair {α : Type} : upair α → set α :=
quotient.lift (λab : α × α, {prod.fst ab, prod.snd ab})
  begin
    intros ab₁ ab₂ h,
    rewrite upair.rel_iff at *,
    exact h
  end

end LoVe
