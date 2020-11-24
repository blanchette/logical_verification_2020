import .love09_hoare_logic_demo


/- # LoVe Exercise 9: Hoare Logic -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Program Verification

The following WHILE program is intended to compute the Gaussian sum up to `n`,
leaving the result in `r`. -/

def GAUSS : stmt :=
stmt.assign "r" (λs, 0) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "r" (λs, s "r" + s "n") ;;
   stmt.assign "n" (λs, s "n" - 1))

/- The summation function: -/

def sum_upto : ℕ → ℕ
| 0       := 0
| (n + 1) := n + 1 + sum_upto n

/- 1.1. Prove the correctness of `GAUSS` using `vcg`. The main challenge is to
figure out which invariant to use for the while loop. The invariant should
capture both the work that has been done already (the intermediate result) and
the work that remains to be done. -/

lemma GAUSS_correct (n₀ : ℕ) :
  {* λs, s "n" = n₀ *} GAUSS {* λs, s "r" = sum_upto n₀ *} :=
show {* λs, s "n" = n₀ *}
     stmt.assign "r" (λs, 0) ;;
     stmt.while_inv (λs, s "r" + sum_upto (s "n") = sum_upto n₀) (λs, s "n" ≠ 0)
       (stmt.assign "r" (λs, s "r" + s "n") ;;
        stmt.assign "n" (λs, s "n" - 1))
     {* λs, s "r" = sum_upto n₀ *}, from
  begin
    vcg; simp [sum_upto] { contextual := tt },
    intro s,
    cases' s "n",
    { simp },
    { simp [nat.succ_eq_add_one, sum_upto],
      cc }
  end

/- 1.2. The following WHILE program is intended to compute the product of `n`
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
show {* λs, s "n" = n₀ ∧ s "m" = m₀ *}
     stmt.assign "r" (λs, 0) ;;
     stmt.while_inv (λs, s "m" = m₀ ∧ s "r" + s "n" * s "m" = n₀ * s "m")
         (λs, s "n" ≠ 0)
       (stmt.assign "r" (λs, s "r" + s "m") ;;
        stmt.assign "n" (λs, s "n" - 1))
     {* λs, s "r" = n₀ * m₀ *}, from
  begin
    vcg; simp { contextual := tt },
    intro s,
    cases' s "n",
    { simp },
    { simp [nat.succ_eq_add_one, mul_add, add_mul],
      cc }
  end


/- ## Question 2: Hoare Triples for Total Correctness -/

def total_hoare (P : state → Prop) (S : stmt) (Q : state → Prop) : Prop :=
∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` Q : 1 ` *]` :=
total_hoare P S Q

namespace total_hoare

/- 2.1. Prove the consequence rule. -/

lemma consequence {P P' Q Q' : state → Prop} {S}
    (hS : [* P *] S [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
  [* P' *] S [* Q' *] :=
begin
  intros s hs,
  cases' hS s (hP s hs) with t ht,
  apply exists.intro t,
  apply and.intro,
  { exact and.elim_left ht },
  { exact hQ t (and.elim_right ht) }
end

/- 2.2. Prove the rule for `skip`. -/

lemma skip_intro {P} :
  [* P *] stmt.skip [* P *] :=
begin
  intros s hs,
  apply exists.intro s,
  exact and.intro big_step.skip hs
end

/- 2.3. Prove the rule for `assign`. -/

lemma assign_intro {P : state → Prop} {x} {a : state → ℕ} :
  [* λs, P (s{x ↦ a s}) *] stmt.assign x a [* P *] :=
begin
  intros s hs,
  apply exists.intro (s{x ↦ a s}),
  exact and.intro big_step.assign hs
end

/- 2.4. Prove the rule for `seq`. -/

lemma seq_intro {P Q R S T} (hS : [* P *] S [* Q *]) (hT : [* Q *] T [* R *]) :
  [* P *] S ;; T [* R *] :=
begin
  intros s hs,
  cases' hS s hs with t hS',
  cases' hT t (and.elim_right hS') with u hT',
  apply exists.intro u,
  apply and.intro,
  { exact big_step.seq (and.elim_left hS') (and.elim_left hT') },
  { exact and.elim_right hT' }
end

/- 2.5. Complete the proof of the rule for `ite`.

Hint: This requires a case distinction on the truth value of `b s`. -/

lemma ite_intro {b P Q : state → Prop} {S T}
    (hS : [* λs, P s ∧ b s *] S [* Q *])
    (hT : [* λs, P s ∧ ¬ b s *] T [* Q *]) :
  [* P *] stmt.ite b S T [* Q *] :=
begin
  intros s hs,
  cases' classical.em (b s),
  { cases' hS s (and.intro hs h) with t ht,
    apply exists.intro t,
    apply and.intro,
    { exact big_step.ite_true h (and.elim_left ht) },
    { exact and.elim_right ht } },
  { cases' hT s (and.intro hs h) with t ht,
    apply exists.intro t,
    apply and.intro,
    { exact big_step.ite_false h (and.elim_left ht) },
    { exact and.elim_right ht } }
end

/- 2.6 (**optional**). Try to prove the rule for `while`.

The rule is parameterized by a loop invariant `I` and by a variant `V` that
decreases with each iteration of the loop body.

Before we prove the desired lemma, we introduce an auxiliary lemma. Its proof
requires well-founded induction. When using `while_var_intro_aux` as induction
hypothesis we recommend to do it directly after proving that the argument is
less than `v₀`:

    have ih : ∃u, (stmt.while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
      have V t < v₀ :=
        …,
      while_var_intro_aux (V t) …,

Similarly to `ite`, the proof requires a case distinction on `b s ∨ ¬ b s`. -/

lemma while_var_intro_aux {b : state → Prop} (I : state → Prop) (V : state → ℕ)
  {S} (h_inv : ∀v₀, [* λs, I s ∧ b s ∧ V s = v₀ *] S [* λs, I s ∧ V s < v₀ *]) :
  ∀v₀ s, V s = v₀ → I s → ∃t, (stmt.while b S, s) ⟹ t ∧ I t ∧ ¬ b t
| v₀ s V_eq hs :=
  begin
    cases' classical.em (b s) with hcs hncs,
    { have h_inv : ∃t, (S, s) ⟹ t ∧ I t ∧ V t < v₀ :=
        h_inv v₀ s (and.intro hs (and.intro hcs V_eq)),
      cases' h_inv with t ht,
      have ih : ∃u, (stmt.while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
        have V t < v₀ :=
          and.elim_right (and.elim_right ht),
        while_var_intro_aux (V t) t (by refl)
          (and.elim_left (and.elim_right ht)),
      cases' ih with u hu,
      apply exists.intro u,
      apply and.intro,
      { exact big_step.while_true hcs (and.elim_left ht) (and.elim_left hu) },
      { exact and.elim_right hu } },
    { apply exists.intro s,
      apply and.intro,
      { exact big_step.while_false hncs },
      { exact and.intro hs hncs } }
  end

lemma while_var_intro {b : state → Prop} (I : state → Prop) (V : state → ℕ) {S}
  (hinv : ∀v₀, [* λs, I s ∧ b s ∧ V s = v₀ *] S [* λs, I s ∧ V s < v₀ *]) :
  [* I *] stmt.while b S [* λs, I s ∧ ¬ b s *] :=
begin
  intros s hs,
  exact while_var_intro_aux I V hinv (V s) s (by refl) hs
end

end total_hoare

end LoVe
