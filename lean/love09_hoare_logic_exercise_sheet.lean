import .love09_hoare_logic_demo


/-! # LoVe Exercise 9: Hoare Logic -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Program Verification

The following WHILE program is intended to compute the Gaussian sum up to `n`,
leaving the result in `r`. -/

def GAUSS : stmt :=
stmt.assign "r" (λs, 0) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "r" (λs, s "r" + s "n") ;;
   stmt.assign "n" (λs, s "n" - 1))

/-! The summation function: -/

def sum_upto : ℕ → ℕ
| 0       := 0
| (n + 1) := n + 1 + sum_upto n

/-! 1.1. Prove the correctness of `GAUSS` using `vcg`. The main challenge is to
figure out which invariant to use for the while loop. The invariant should
capture both the work that has been done already (the intermediate result) and
the work that remains to be done. -/

lemma GAUSS_correct (n₀ : ℕ) :
  {* λs, s "n" = n₀ *} GAUSS {* λs, s "r" = sum_upto n₀ *} :=
sorry

/-! 1.2. The following WHILE program is intended to compute the product of `n`
and `m`, leaving the result in `r`. Prove its correctness using `vcg`.

Hint: If a variable `x` does not change in a program, it might be useful to
record this in the invariant, by adding a conjunct `s "x" = x₀`. -/

def MUL : stmt :=
stmt.assign "r" (λs, 0) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "r" (λs, s "r" + s "m") ;;
   stmt.assign "n" (λs, s "n" - 1))

lemma MUL_correct (n₀ m₀ : ℕ) :
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *} MUL {* λs, s "r" = n₀ * m₀ *} :=
sorry


/-! ## Question 2: Hoare Triples for Total Correctness -/

def total_hoare (P : state → Prop) (S : stmt) (Q : state → Prop) : Prop :=
∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` Q : 1 ` *]` :=
total_hoare P S Q

namespace total_hoare

/-! 2.1. Prove the consequence rule. -/

lemma consequence {P P' Q Q' : state → Prop} {S}
    (hS : [* P *] S [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
  [* P' *] S [* Q' *] :=
sorry

/-! 2.2. Prove the rule for `skip`. -/

lemma skip_intro {P} :
  [* P *] stmt.skip [* P *] :=
sorry

/-! 2.3. Prove the rule for `assign`. -/

lemma assign_intro {P : state → Prop} {x} {a : state → ℕ} :
  [* λs, P (s{x ↦ a s}) *] stmt.assign x a [* P *] :=
sorry

/-! 2.4. Prove the rule for `seq`. -/

lemma seq_intro {P Q R S T} (hS : [* P *] S [* Q *]) (hT : [* Q *] T [* R *]) :
  [* P *] S ;; T [* R *] :=
sorry

/-! 2.5. Complete the proof of the rule for `ite`.

Hint: This requires a case distinction on the truth value of `b s`. -/

lemma ite_intro {b P Q : state → Prop} {S T}
    (hS : [* λs, P s ∧ b s *] S [* Q *])
    (hT : [* λs, P s ∧ ¬ b s *] T [* Q *]) :
  [* P *] stmt.ite b S T [* Q *] :=
sorry

/-! 2.6 (**optional**). Try to prove the rule for `while`.

The rule is parameterized by a loop invariant `I` and by a variant `V` that
decreases with each iteration of the loop body.

Before we prove the desired lemma, we introduce an auxiliary lemma. Its proof
requires well-founded induction. When using `while_intro.aux` as induction
hypothesis we recommend to do it directly after proving that the argument is
less than `v₀`:

    have ih : ∃u, (stmt.while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
      have V t < v₀ :=
        …,
      while_intro.aux (V t) …,

Similarly to `ite`, the proof requires a case distinction on `b s ∨ ¬ b s`. -/

lemma while_intro.aux {b : state → Prop} (I : state → Prop) (V : state → ℕ) {S}
  (h_inv : ∀v₀, [* λs, I s ∧ b s ∧ V s = v₀ *] S [* λs, I s ∧ V s < v₀ *]) :
  ∀v₀ s, V s = v₀ → I s → ∃t, (stmt.while b S, s) ⟹ t ∧ I t ∧ ¬ b t
| v₀ s V_eq hs :=
sorry

lemma while_intro {b : state → Prop} (I : state → Prop) (V : state → ℕ) {S}
  (hinv : ∀v₀, [* λs, I s ∧ b s ∧ V s = v₀ *] S [* λs, I s ∧ V s < v₀ *]) :
  [* I *] stmt.while b S [* λs, I s ∧ ¬ b s *] :=
sorry

end total_hoare

end LoVe
