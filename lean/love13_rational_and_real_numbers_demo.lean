import .lovelib


/- # LoVe Demo 13: Rational and Real Numbers

We review the construction of `ℚ` and `ℝ` as quotient types.

A procedure to construct types with specific properties:

1. Create a new type that can represent all elements, but not necessarily in a
   unique manner.

2. Quotient this representation, equating elements that should be equal.

3. Define operators on the quotient type by lifting functions from the base
   type and prove that they are compatible with the quotient relation.

We used this approach in lecture 11 to construct `ℤ`. It can be used for
`ℚ` and `ℝ` as well. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Rational Numbers

**Step 1:** A rational number is a number that can be expressed as a fraction
`n / d` of integers `n` and `d ≠ 0`: -/

structure fraction :=
(num           : ℤ)
(denom         : ℤ)
(denom_ne_zero : denom ≠ 0)

/- The number `n` is called the numerator, and the number `d` is called the
denominator.

The representation of a rational number as a fraction is not unique—e.g.,
`1 / 2 = 2 / 4 = -1 / -2`.

**Step 2:** Two fractions `n₁ / d₁` and `n₂ / d₂` represent the same rational
number if the ratio between numerator and denominator are the same—i.e.,
`n₁ * d₂ = n₂ * d₁`. This will be our equivalence relation `≈` on fractions. -/

namespace fraction

@[instance] def setoid : setoid fraction :=
{ r     := λa b : fraction, num a * denom b = num b * denom a,
  iseqv :=
    begin
      repeat { apply and.intro },
      { intros a; refl },
      { intros a b h; cc },
      { intros a b c eq_ab eq_bc,
        apply int.eq_of_mul_eq_mul_right (denom_ne_zero b),
        cc }
    end }

lemma setoid_iff (a b : fraction) :
  a ≈ b ↔ num a * denom b = num b * denom a :=
by refl

/- **Step 3:** Define `0 := 0 / 1`, `1 := 1 / 1`, addition, multiplication, etc.

    `n₁ / d₁ + n₂ / d₂`     := `(n₁ * d₂ + n₂ * d₁) / (d₁ * d₂)`
    `(n₁ / d₁) * (n₂ / d₂)` := `(n₁ * n₂) / (d₁ * d₂)`

Then show that they are compatible with `≈`. -/

def of_int (i : ℤ) : fraction :=
{ num           := i,
  denom         := 1,
  denom_ne_zero := by simp }

@[instance] def has_zero : has_zero fraction :=
{ zero := of_int 0 }

@[instance] def has_one : has_one fraction :=
{ one := of_int 1 }

@[instance] def has_add : has_add fraction :=
{ add := λa b : fraction,
    { num           := num a * denom b + num b * denom a,
      denom         := denom a * denom b,
      denom_ne_zero :=
        by apply mul_ne_zero; exact denom_ne_zero _ } }

@[simp] lemma add_num (a b : fraction) :
  num (a + b) = num a * denom b + num b * denom a :=
by refl

@[simp] lemma add_denom (a b : fraction) :
  denom (a + b) = denom a * denom b :=
by refl

lemma add_equiv_add {a a' b b' : fraction} (ha : a ≈ a')
    (hb : b ≈ b') :
  a + b ≈ a' + b' :=
begin
  simp [setoid_iff, add_denom, add_num] at *,
  calc  (num a * denom b + num b * denom a)
          * (denom a' * denom b')
      = num a * denom a' * denom b * denom b'
          + num b * denom b' * denom a * denom a' :
    by simp [add_mul, mul_add]; ac_refl
  ... = num a' * denom a * denom b * denom b'
          + num b' * denom b * denom a * denom a' :
    by simp [*]
  ... = (num a' * denom b' + num b' * denom a')
          * (denom a * denom b) :
    by simp [add_mul, mul_add]; ac_refl
end

@[instance] def has_neg : has_neg fraction :=
{ neg := λa : fraction,
    { num := - num a,
      ..a } }

@[simp] lemma neg_num (a : fraction) :
  num (- a) = - num a :=
by refl

@[simp] lemma neg_denom (a : fraction) :
  denom (- a) = denom a :=
by refl

lemma setoid_neg {a a' : fraction} (hab : a ≈ a') :
  - a ≈ - a' :=
by simp [setoid_iff] at hab ⊢; exact hab

@[instance] def has_mul : has_mul fraction :=
{ mul := λa b : fraction,
    { num           := num a * num b,
      denom         := denom a * denom b,
      denom_ne_zero :=
        mul_ne_zero (denom_ne_zero a) (denom_ne_zero b) } }

@[simp] lemma mul_num (a b : fraction) :
  num (a * b) = num a * num b :=
by refl

@[simp] lemma mul_denom (a b : fraction) :
  denom (a * b) = denom a * denom b :=
by refl

lemma setoid_mul {a a' b b' : fraction} (ha : a ≈ a')
    (hb : b ≈ b') :
  a * b ≈ a' * b' :=
by simp [setoid_iff] at ha hb ⊢; cc

@[instance] def has_inv : has_inv fraction :=
{ inv := λa : fraction,
    if ha : num a = 0 then
      0
    else
      { num           := denom a,
        denom         := num a,
        denom_ne_zero := ha } }

lemma inv_def (a : fraction) (ha : num a ≠ 0) :
  a⁻¹ =
  { num           := denom a,
    denom         := num a,
    denom_ne_zero := ha } :=
dif_neg ha

lemma inv_zero (a : fraction) (ha : num a = 0) :
  a⁻¹ = 0 :=
dif_pos ha

@[simp] lemma inv_num (a : fraction) (ha : num a ≠ 0) :
  num (a⁻¹) = denom a :=
by rw inv_def a ha

@[simp] lemma inv_denom (a : fraction) (ha : num a ≠ 0) :
  denom (a⁻¹) = num a :=
by rw inv_def a ha

lemma setoid_inv {a a' : fraction} (ha : a ≈ a') :
  a⁻¹ ≈ a'⁻¹ :=
begin
  cases' classical.em (num a = 0),
  case inl : ha0 {
    cases' classical.em (num a' = 0),
    case inl : ha'0 {
      simp [ha0, ha'0, inv_zero] },
    case inr : ha'0 {
      simp [ha0, ha'0, setoid_iff, denom_ne_zero] at ha,
      cc } },
  case inr : ha0 {
    cases' classical.em (num a' = 0),
    case inl : ha'0 {
      simp [setoid_iff, ha'0, denom_ne_zero] at ha,
      cc },
    case inr : ha'0 {
      simp [setoid_iff, ha0, ha'0] at ha ⊢,
      cc } }
end

end fraction

def rat : Type :=
quotient fraction.setoid

namespace rat

@[instance] def has_zero : has_zero rat :=
{ zero := ⟦0⟧ }

@[instance] def has_one : has_one rat :=
{ one := ⟦1⟧ }

@[instance] def has_add : has_add rat :=
{ add := quotient.lift₂ (λa b : fraction, ⟦a + b⟧)
    begin
      intros a b a' b' ha hb,
      apply quotient.sound,
      exact fraction.add_equiv_add ha hb
    end }

@[instance] def has_neg : has_neg rat :=
{ neg := quotient.lift (λa : fraction, ⟦- a⟧)
    begin
      intros a a' ha,
      apply quotient.sound,
      exact fraction.setoid_neg ha
    end }

@[instance] def has_mul : has_mul rat :=
{ mul := quotient.lift₂ (λa b : fraction, ⟦a * b⟧)
    begin
      intros a b a' b' ha hb,
      apply quotient.sound,
      exact fraction.setoid_mul ha hb
    end }

@[instance] def has_inv : has_inv rat :=
{ inv := quotient.lift (λa : fraction, ⟦a⁻¹⟧)
    begin
      intros a a' ha,
      apply quotient.sound,
      exact fraction.setoid_inv ha
    end }

end rat


/- ### Alternative Definitions of `ℚ`

**Alternative 1:** Define `ℚ` as a subtype of `fraction`, with the requirement
that the numerator and the denominator have no common divisors except `1` and
`-1`: -/

namespace alternative_1

def rat.is_canonical (a : fraction) : Prop :=
nat.coprime (int.nat_abs (fraction.num a))
  (int.nat_abs (fraction.denom a))

def rat := {a : fraction // rat.is_canonical a}

end alternative_1

/- This is more or less the `mathlib` definition.

Advantages:

* no quotient required;
* more efficient computation;
* more properties are syntactic equalities up to computation.

Disadvantage:

* more complicated function definitions.

**Alternative 2**: Define all elements syntactically, including the desired
operations: -/

namespace alternative_2

inductive pre_rat : Type
| zero : pre_rat
| one  : pre_rat
| add  : pre_rat → pre_rat → pre_rat
| sub  : pre_rat → pre_rat → pre_rat
| mul  : pre_rat → pre_rat → pre_rat
| div  : pre_rat → pre_rat → pre_rat

/- Then quotient `pre_rat` to enforce congruence rules and the field axioms: -/

inductive rat.rel : pre_rat → pre_rat → Prop
| add_congr {a b c d : pre_rat} :
  rat.rel a b → rat.rel c d →
  rat.rel (pre_rat.add a c) (pre_rat.add b d)
| add_assoc {a b c : pre_rat} :
  rat.rel (pre_rat.add a (pre_rat.add b c))
    (pre_rat.add (pre_rat.add a b) c)
| zero_add {a : pre_rat} :
  rat.rel (pre_rat.add pre_rat.zero a) a
-- etc.

def rat : Type :=
quot rat.rel

end alternative_2

/- Advantages:

* no dependency on `ℤ`;
* easy proofs of the field axioms;
* general recipe reusable for other algebraic constructions (e.g., free monoids,
  free groups).

Disadvantage:

* the definition of orders and lemmas about them are more complicated.


### Real Numbers

Some sequences of rational numbers seem to converge because the numbers in the
sequence get closer and closer to each other, and yet do not converge to a
rational number.

Example:

    `a₀ = 1`
    `a₁ = 1.4`
    `a₂ = 1.41`
    `a₃ = 1.414`
    `a₄ = 1.4142`
    `a₅ = 1.41421`
    `a₆ = 1.414213`
    `a₇ = 1.4142135`
       ⋮

This sequence seems to converge because each `a_n` is at most `10^-n` away from
any of the following numbers. But the limit is `√2`, which is not a rational
number.

The rational numbers are incomplete, and the reals are their  __completion__.

To construct the reals, we need to fill in the gaps that are revealed by these
sequences that seem to converge, but do not.

Mathematically, a sequence `a₀, a₁, …` of rational numbers is __Cauchy__ if for
any `ε > 0`, there exists an `N ∈ ℕ` such that for all `m ≥ N`, we have
`|a_N - a_m| < ε`.

In other words, no matter how small we choose `ε`, we can always find a point in
the sequence from which all following numbers deviate less than by `ε`. -/

def is_cau_seq (f : ℕ → ℚ) : Prop :=
∀ε > 0, ∃N, ∀m ≥ N, abs (f N - f m) < ε

/- Not every sequence is a Cauchy sequence: -/

lemma id_not_cau_seq :
  ¬ is_cau_seq (λn : ℕ, (n : ℚ)) :=
begin
  rw is_cau_seq,
  intro h,
  cases' h 1 zero_lt_one with i hi,
  have hi_succi :=
    hi (i + 1) (by simp),
  simp [←sub_sub] at hi_succi,
  linarith
end

/- We define a type of Cauchy sequences as a subtype: -/

def cau_seq : Type :=
{f : ℕ → ℚ // is_cau_seq f}

def seq_of (f : cau_seq) : ℕ → ℚ :=
subtype.val f

/- Cauchy sequences represent real numbers:

* `a_n = 1 / n` represents the real number `0`;
* `1, 1.4, 1.41, …` represents the real number `√2`;
* `a_n = 0` also represents the real number `0`.

Since different Cauchy sequences can represent the same real number, we need to
take the quotient. Formally, two sequences represent the same real number when
their difference converges to zero: -/

namespace cau_seq

@[instance] def setoid : setoid cau_seq :=
{ r     := λf g : cau_seq,
    ∀ε > 0, ∃N, ∀m ≥ N, abs (seq_of f m - seq_of g m) < ε,
  iseqv :=
    begin
      apply and.intro,
      { intros f ε hε,
        apply exists.intro 0,
        finish },
      apply and.intro,
      { intros f g hfg ε hε,
        cases' hfg ε hε with N hN,
        apply exists.intro N,
        intros m hm,
        rw abs_sub,
        apply hN m hm },
      { intros f g h hfg hgh ε hε,
        cases' hfg (ε / 2) (half_pos hε) with N₁ hN₁,
        cases' hgh (ε / 2) (half_pos hε) with N₂ hN₂,
        apply exists.intro (max N₁ N₂),
        intros m hm,
        calc  abs (seq_of f m - seq_of h m)
            ≤ abs (seq_of f m - seq_of g m)
              + abs (seq_of g m - seq_of h m) :
          by apply abs_sub_le
        ... < ε / 2 + ε / 2 :
          add_lt_add (hN₁ m (le_of_max_le_left hm))
            (hN₂ m (le_of_max_le_right hm))
        ... = ε :
          by simp }
    end }

lemma setoid_iff (f g : cau_seq) :
  f ≈ g ↔
  ∀ε > 0, ∃N, ∀m ≥ N, abs (seq_of f m - seq_of g m) < ε :=
by refl

/- We can define constants such as `0` and `1` as a constant sequence. Any
constant sequence is a Cauchy sequence: -/

def const (q : ℚ) : cau_seq :=
subtype.mk (λ_ : ℕ, q) (by rw is_cau_seq; intros ε hε; finish)

/- Defining addition of real numbers requires a little more effort. We define
addition on Cauchy sequences as pairwise addition: -/

@[instance] def has_add : has_add cau_seq :=
{ add := λf g : cau_seq,
    subtype.mk (λn : ℕ, seq_of f n + seq_of g n) sorry }

/- Above, we omit the proof that the addition of two Cauchy sequences is again
a Cauchy sequence.

Next, we need to show that this addition is compatible with `≈`: -/

lemma add_equiv_add {f f' g g' : cau_seq} (hf : f ≈ f')
    (hg : g ≈ g') :
  f + g ≈ f' + g' :=
begin
  intros ε₀ hε₀,
  simp [setoid_iff],
  cases' hf (ε₀ / 2) (half_pos hε₀) with Nf hNf,
  cases' hg (ε₀ / 2) (half_pos hε₀) with Ng hNg,
  apply exists.intro (max Nf Ng),
  intros m hm,
  calc  abs (seq_of (f + g) m - seq_of (f' + g') m)
      = abs ((seq_of f m + seq_of g m)
           - (seq_of f' m + seq_of g' m)) :
    by refl
  ... = abs ((seq_of f m - seq_of f' m)
           + (seq_of g m - seq_of g' m)) :
    begin
      have arg_eq :
        seq_of f m + seq_of g m - (seq_of f' m + seq_of g' m) =
        seq_of f m - seq_of f' m + (seq_of g m - seq_of g' m),
        by linarith,
      rw arg_eq
    end
  ... ≤ abs (seq_of f m - seq_of f' m)
      + abs (seq_of g m - seq_of g' m) :
    by apply abs_add
  ... < ε₀ / 2 + ε₀ / 2 :
    add_lt_add (hNf m (le_of_max_le_left hm))
      (hNg m (le_of_max_le_right hm))
  ... = ε₀ :
    by simp
end

end cau_seq

/- The real numbers are the quotient: -/

def real : Type :=
quotient cau_seq.setoid

namespace real

@[instance] def has_zero : has_zero real :=
{ zero := ⟦cau_seq.const 0⟧ }

@[instance] def has_one : has_one real :=
{ one := ⟦cau_seq.const 1⟧ }

@[instance] def has_add : has_add real :=
{ add := quotient.lift₂ (λa b : cau_seq, ⟦a + b⟧)
    begin
      intros a b a' b' ha hb,
      apply quotient.sound,
      exact cau_seq.add_equiv_add ha hb,
    end }

end real


/- ### Alternative Definitions of `ℝ`

* Dedekind cuts: `r : ℝ` is represented essentially as `{x : ℚ | x < r}`.

* Binary sequences `ℕ → bool` can represent the interval `[0, 1]`. This can be
  used to build `ℝ`. -/

end LoVe
