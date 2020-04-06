import .love05_inductive_predicates_demo


/-! # LoVe Demo 12: Basic Mathematical Structures

We introduce definitions and proofs about basic mathematical structures such as
groups, fields, and linear orders. -/


set_option pp.beta true

namespace LoVe


/-! ## Type Classes over a Single Binary Operator

Mathematically, a __group__ is a set `G` with a binary operator `• : G × G → G`
with the following properties, called __group axioms__:

* Associativity: For all `a, b, c ∈ G`, we have `(a • b) • c = a • (b • c)`.
* Identity element: There exists an element `e ∈ G` such that for all `a ∈ G`,
  we have `e • a = a`.
* Inverse element: For each `a ∈ G`, there exists an inverse element
  `inv(a) ∈ G` such that `inv(a) • a = e`.

Examples of groups are
* `ℤ` with `+`;
* `ℝ` with `+`;
* `ℝ \ {0}` with `*`.

In Lean, a type class for groups can be defined as follows: -/

namespace monolithic_group

@[class] structure group (α : Type) : Type :=
(mul          : α → α → α)
(one          : α)
(inv          : α → α)
(mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c))
(one_mul      : ∀a, mul one a = a)
(mul_left_inv : ∀a, mul (inv a) a = one)

end monolithic_group

/-! In Lean, however, group is part of a larger hierarchy of algebraic
structures:

Type class               | Properties                               | Examples
------------------------ | -----------------------------------------|-------------------
`semigroup`              | associativity of `*`                     | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`monoid`                 | `semigroup` with unit `1`                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`left_cancel_semigroup`  | `semigroup` with `c * a = c * b → a = b` |
`right_cancel_semigroup` | `semigroup` with `a * c = b * c → a = b` |
`group`                  | `monoid` with inverse `⁻¹`               |

Most of these structures have commutative versions: `comm_semigroup`,
`comm_monoid`, `comm_group`.

The __multiplicative__ structures (over `*`, `1`, `⁻¹`) are copied to produce
__additive__ versions (over `+`, `0`, `-`):

Type class                   | Properties                                   | Examples
---------------------------- | ---------------------------------------------|-------------------
`add_semigroup`              | associativity of `+`                         | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`add_monoid`                 | `add_semigroup` with unit `0`                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`add_left_cancel_semigroup`  | `add_semigroup` with `c + a = c + b → a = b` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`add_right_cancel_semigroup` | `add_semigroup` with `a + c = b + c → a = b` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`add_group`                  | `add_monoid` with inverse `-`                | `ℝ`, `ℚ`, `ℤ` -/

#print group
#print add_group

/-! Let us define our own type, of integers modulo 2, and register it as an
additive group. -/

inductive ℤ₂ : Type
| zero
| one

def ℤ₂.add : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.zero a       := a
| a       ℤ₂.zero := a
| ℤ₂.one  ℤ₂.one  := ℤ₂.zero

@[instance] def ℤ₂.add_group : add_group ℤ₂ :=
{ add          := ℤ₂.add,
  add_assoc    :=
    by intros a b c; simp [(+)]; cases a; cases b; cases c;
      refl,
  zero         := ℤ₂.zero,
  zero_add     := by intro a; cases a; refl,
  add_zero     := by intro a; cases a; refl,
  neg          := λa, a,
  add_left_neg := by intro a; cases a; refl }

#reduce ℤ₂.one + 0 - 0 - ℤ₂.one

lemma ℤ₂.add_right_neg:
  ∀a : ℤ₂, a + - a = 0 :=
add_right_neg

/-! Another example: Lists are an `add_monoid`: -/

@[instance] def list.add_monoid {α : Type} :
  add_monoid (list α) :=
{ zero      := [],
  add       := (++),
  add_assoc := list.append_assoc,
  zero_add  := list.nil_append,
  add_zero  := list.append_nil }


/-! ## Type Classes with Two Binary Operators

Mathematically, a __field__ is a set `F` such that

* `F` forms a commutative group under an operator `+`, called addition, with
  identity element `0`.
* `F\{0}` forms a commutative group under an operator `*`, called
  multiplication.
* Multiplication distributes over addition—i.e.,
  `a * (b + c) = a * b + a * c` for all `a, b, c ∈ F`.

In Lean, fields are also part of a larger hierarchy:

Type class       |  Properties                                         | Examples
-----------------|-----------------------------------------------------|-------------------
`semiring`       | `monoid` and `add_comm_monoid` with distributivity  | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`comm_semiring`  | `semiring` with commutativity of `*`                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`ring`           | `monoid` and `add_comm_group` with distributivity   | `ℝ`, `ℚ`, `ℤ`
`comm_ring`      | `ring` with commutativity of `*`                    | `ℝ`, `ℚ`, `ℤ`
`division_ring`  | `ring` with multiplicative inverse `⁻¹`             | `ℝ`, `ℚ`
`field`          | `division_ring` with commutativity of `*`           | `ℝ`, `ℚ`
`discrete_field` | `field` with decidable equality and `∀n, n / 0 = 0` | `ℝ`, `ℚ` -/

#print field

/-! Let us continue with our example: -/

def ℤ₂.mul : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.one  a       := a
| a       ℤ₂.one  := a
| ℤ₂.zero ℤ₂.zero := ℤ₂.zero

@[instance] def ℤ₂.field : field ℤ₂ :=
{ one            := ℤ₂.one,
  mul            := ℤ₂.mul,
  inv            := λa, a,
  add_comm       := by intros a b; cases a; cases b; refl,
  zero_ne_one    := by finish,
  one_mul        := by intros a; cases a; refl,
  mul_one        := by intros a; cases a; refl,
  mul_inv_cancel := by intros a h; cases a; finish,
  inv_mul_cancel := by intros a h; cases a; finish,
  mul_assoc      :=
    by intros a b c; cases a; cases b; cases c; refl,
  mul_comm       := by intros a b; cases a; cases b; refl,
  left_distrib   :=
    by intros a b c; by cases a; cases b; cases c; refl,
  right_distrib  :=
    by intros a b c; by cases a; cases b; cases c; refl,
  ..ℤ₂.add_group }

#reduce (1 : ℤ₂) * 0 / (0 - 1)

#reduce (3 : ℤ₂)

lemma ring_example (a b : ℤ₂) :
  (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 :=
by ring

lemma ring_exp_example (a b : ℤ₂) (n : ℕ):
  (a + b) ^ (2 + n) =
  (a + b) ^ n * (a ^ 2 + 2 * a * b + b ^ 2) :=
by ring_exp

/-! `ring` and `ring_exp` prove equalities over commutative rings and semirings
by normalizing expressions. The `ring_exp` variant also normalizes exponents. -/

lemma abel_example (a b : ℤ) :
  a + b + 0 - (b + a + a) = - a :=
by abel

/-! `abel` proves equalities over additive commutative monoids and groups by
normalizing expressions.


## Coercions

When combining numbers form `ℕ`, `ℤ`, `ℚ`, and `ℝ`, we might want to cast from
one type to another. Lean has a mechanism to automatically introduce coercions,
represented by `coe` (syntactic sugar: `↑`). `coe` can be set up to provide
implicit coercions between arbitrary types.

Many coercions are already in place, including the following:

* `coe : ℕ → α` casts `ℕ` to another semiring `α`;
* `coe : ℤ → α` casts `ℤ` to another ring `α`;
* `coe : ℚ → α` casts `ℚ` to another division ring `α`.

For example, this works, although negation `- n` is not defined on natural
numbers: -/

lemma neg_mul_neg_nat (n : ℕ) (z : ℤ) :
  (- z) * (- n) = z * n :=
neg_mul_neg z n

/-! Notice how Lean introduced a `↑` coercion: -/

#print neg_mul_neg_nat

/-! Another example: -/

lemma neg_nat_mul_neg (n : ℕ) (z : ℤ) :
  (- n : ℤ) * (- z) = n * z :=
neg_mul_neg n z

#print neg_nat_mul_neg

/-! In proofs involving coercions, the tactic `norm_cast` can be convenient. -/

lemma norm_cast_example_1 (m n : ℕ) (h : (m : ℤ) = (n : ℤ)) :
  m = n :=
begin
  norm_cast at h,
  exact h
end

lemma norm_cast_example_2 (m n : ℕ) :
  (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
by norm_cast

/-! `norm_cast` moves coercions towards the inside of expressions, as a form of
simplification. Like `simp`, it will generally produce a subgoal.

`norm_cast` relies on lemmas such as the following: -/

#check nat.cast_add
#check int.cast_add
#check rat.cast_add


/-! ### Lists, Multisets and Finite Sets

For finite collections of elements different structures are available:

* lists: order and duplicates matter;
* multisets: only duplicates matter;
* finsets: neither order nor duplicates matter. -/

lemma list_duplicates_example :
  [2, 3, 3, 4] ≠ [2, 3, 4] :=
dec_trivial

lemma list_order_example :
  [4, 3, 2] ≠ [2, 3, 4] :=
dec_trivial

lemma multiset_duplicates_example :
  ({2, 3, 3, 4} : multiset ℕ) ≠ {2, 3, 4} :=
dec_trivial

lemma multiset_order_example :
  ({2, 3, 4} : multiset ℕ) = {4, 3, 2} :=
dec_trivial

lemma finset_duplicates_example :
  ({2, 3, 3, 4} : finset ℕ) = {2, 3, 4} :=
dec_trivial

lemma finsetorder_example :
  ({2, 3, 4} : finset ℕ) = {4, 3, 2} :=
dec_trivial

def list.elems : btree ℕ → list ℕ
| btree.empty        := []
| (btree.node a l r) := a :: list.elems l ++ list.elems r

def multiset.elems : btree ℕ → multiset ℕ
| btree.empty        := ∅
| (btree.node a l r) :=
  {a} ∪ (multiset.elems l ∪ multiset.elems r)

def finset.elems : btree ℕ → finset ℕ
| btree.empty        := ∅
| (btree.node a l r) := {a} ∪ (finset.elems l ∪ finset.elems r)

#eval list.sum [2, 3, 4]                          -- result: 9
#eval multiset.sum ({2, 3, 4} : multiset ℕ)       -- result: 9
#eval finset.sum ({2, 3, 4} : finset ℕ) (λn, n)   -- result: 9

#eval list.prod [2, 3, 4]                         -- result: 24
#eval multiset.prod ({2, 3, 4} : multiset ℕ)      -- result: 24
#eval finset.prod ({2, 3, 4} : finset ℕ) (λn, n)  -- result: 24


/-! ## Order Type Classes

Many of the structures introduced above can be ordered. For example, the
well-known order on the natural numbers can be defined as follows: -/

inductive nat.le : ℕ → ℕ → Prop
| refl : ∀a : ℕ, nat.le a a
| step : ∀a b : ℕ, nat.le a b → nat.le a (b + 1)

/-! This is an example of a linear order. A __linear order__ (or
__total order__) is a binary relation `≤` such that for all `a`, `b`, `c`, the
following properties hold:

* Reflexivity: `a ≤ a`.
* Transitivity: If `a ≤ b` and `b ≤ c`, then `a ≤ c`.
* Antisymmetry: If `a ≤ b` and `b ≤ a`, then `a = b`.
* Totality: `a ≤ b` or `b ≤ a`.

If a relation has the first three properties, it is a __partial order__. An
example is `⊆` on sets, finite sets, or multisets. If a relation has the first
two properties, it is a __preorder__. An example is comparing lists by their
length.

In Lean, there are type classes for these different kinds of orders:
`linear_order`, `partial_order`, and `preorder`. The `preorder` class has the
fields

    `le       : α → α → Prop`
    `le_refl  : ∀a : α, le a a`
    `le_trans : ∀a b c : α, le a b → le b c → le a c`

The `partial_order` class also has

    `le_antisymm : ∀a b : α, le a b → le b a → a = b`

and `linear_order` also has

    `le_total : ∀a b : α, le a b ∨ le b a`

We can declare the preorder on lists that compares lists by their length as
follows: -/

@[instance] def list.length.preord {α : Type} :
  preorder (list α) :=
{ le       := λxs ys, list.length xs ≤ list.length ys,
  le_refl  := by intro xs; exact nat.le_refl _,
  le_trans := by intros xs ys zs; exact nat.le_trans }

/-! This instance introduces the infix syntax `≤` and the relations `≥`, `<`,
and `>`: -/

lemma list.length.preord_example {α : Type} (c : α) :
  [c] > [] :=
dec_trivial

/-! Complete lattices (lecture 10) are formalized as another type class,
`complete_lattice`, which inherits from `partial_order`.

Type classes combining orders and algebraic structures are also available:

    `ordered_cancel_comm_monoid`
    `ordered_comm_group ordered_semiring`
    `linear_ordered_semiring`
    `linear_ordered_comm_ring`
    `linear_ordered_field`

All these mathematical structures relate `≤` and `<` with `0`, `1`, `+`, and `*`
by monotonicity rules (e.g., `a ≤ b → c ≤ d → a + c ≤ b + d`) and cancellation
rules (e.g., `c + a ≤ c + b → a ≤ b`). -/

end LoVe
