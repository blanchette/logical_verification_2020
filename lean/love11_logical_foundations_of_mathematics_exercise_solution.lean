import .love11_logical_foundations_of_mathematics_demo


/- # LoVe Exercise 11: Logical Foundations of Mathematics -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check vector

/- The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer function is
truncated. -/

def list.add : list ℤ → list ℤ → list ℤ
| []        []        := []
| (x :: xs) (y :: ys) := (x + y) :: list.add xs ys
| []        (y :: ys) := []
| (x :: xs) []        := []

/- 1.1. Show that if the lists have the same length, the resulting list also
has that length. -/

lemma list.length_add :
  ∀(xs : list ℤ) (ys : list ℤ) (h : list.length xs = list.length ys),
    list.length (list.add xs ys) = list.length xs
| []        []        :=
  by simp [list.add]
| (x :: xs) (y :: ys) :=
  begin
    simp [list.add, length],
    intro h,
    rw list.length_add xs ys h
  end
| []        (y :: ys) :=
  begin
    intro h,
    cases' h
  end
| (x :: xs) []        :=
  begin
    intro h,
    cases' h
  end

/- 1.2. Define componentwise addition on vectors using `list.add` and
`list.length_add`. -/

def vector.add {n : ℕ} : vector ℤ n → vector ℤ n → vector ℤ n
| u v := subtype.mk (list.add (subtype.val u) (subtype.val v))
  begin
    rw list.length_add,
    { exact subtype.property u },
    { rw subtype.property u, rw subtype.property v }
  end

/- 1.3. Show that `list.add` and `vector.add` are commutative. -/

lemma list.add.comm :
  ∀(xs : list ℤ) (ys : list ℤ), list.add xs ys = list.add ys xs
| []        []        := by refl
| (x :: xs) (y :: ys) := by simp [list.add, add_comm]; exact list.add.comm xs ys
| []        (y :: ys) := by refl
| (x :: xs) []        := by refl

lemma vector.add.comm {n : ℕ} (x y : vector ℤ n) :
  vector.add x y = vector.add y x :=
begin
  apply subtype.eq,
  simp [vector.add],
  apply list.add.comm
end


/- ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `int` (= `ℤ`): -/

#check int.rel
#check int.rel_iff
#check int

/- 2.1. Define negation on these integers. -/

def int.neg : int → int :=
quotient.lift (λpn : ℕ × ℕ, ⟦(prod.snd pn, prod.fst pn)⟧)
  begin
    intros a a' ha,
    cases' a with p n,
    cases' a' with p' n',
    apply quotient.sound,
    simp at *,
    rw int.rel_iff at *,
    cc
  end

/- 2.2. Prove the following lemmas about negation. -/

lemma int.neg_eq (p n : ℕ) :
  int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
by refl

lemma int.neg_neg (a : int) :
  int.neg (int.neg a) = a :=
begin
  apply quotient.induction_on a,
  intro a,
  cases' a,
  simp [int.neg_eq]
end

end LoVe
