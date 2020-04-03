import .love05_inductive_predicates_demo
import .love13_rational_and_real_numbers_demo


/-! # LoVe Exercise 13: Rational and Real Numbers -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Rationals

1.1. Prove the following lemma.

Hint: The lemma `fraction.mk.inj_eq` might be useful. -/

#check fraction.mk.inj_eq

lemma fraction.ext (a b : fraction) (hnum : fraction.num a = fraction.num b)
    (hdenom : fraction.denom a = fraction.denom b) :
  a = b :=
sorry

/-! 1.2. Extending the `fraction.has_mul` instance from the lecture, declare
`fraction` as an instance of `semigroup`.

Hint: Use the lemma `fraction.ext` above, and possibly `fraction.mul_num`, and
`fraction.mul_denom`. -/

#check fraction.ext
#check fraction.mul_num
#check fraction.mul_denom

@[instance] def fraction.semigroup : semigroup fraction :=
{ mul_assoc :=
    sorry,
  ..fraction.has_mul }

/-! 1.3. Extending the `rat.has_mul` instance from the lecture, declare `rat` as
an instance of `semigroup`. -/

@[instance] def rat.semigroup : semigroup rat :=
{ mul_assoc :=
    sorry,
  ..rat.has_mul }

end LoVe
