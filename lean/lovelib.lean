import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where


/-! # LoVe Library

This files contains a few extensions on top of Lean's core libraries and
`mathlib`. -/


namespace LoVe


/-! ## Structured Proofs -/

notation `fix ` binders `, ` r:(scoped f, f) := r


/-! ## Logical Connectives -/

attribute [pattern] or.intro_left or.intro_right

meta def tactic.dec_trivial := `[exact dec_trivial]

lemma not_def (a : Prop) :
  ¬ a ↔ a → false :=
by refl

@[simp] lemma not_not_iff (a : Prop) [decidable a] :
  ¬¬ a ↔ a :=
by by_cases a; simp [h]

@[simp] lemma and_imp_distrib (a b c : Prop) :
  (a ∧ b → c) ↔ (a → b → c) :=
iff.intro
  (assume h ha hb, h ⟨ha, hb⟩)
  (assume h ⟨ha, hb⟩, h ha hb)

@[simp] lemma or_imp_distrib {a b c : Prop} :
  a ∨ b → c ↔ (a → c) ∧ (b → c) :=
iff.intro
  (assume h,
   ⟨assume ha, h (or.intro_left _ ha), assume hb, h (or.intro_right _ hb)⟩)
  (assume ⟨ha, hb⟩ h, match h with or.inl h := ha h | or.inr h := hb h end)

@[simp] lemma exists_imp_distrib {α : Sort*} {p : α → Prop} {a : Prop} :
  ((∃x, p x) → a) ↔ (∀x, p x → a) :=
iff.intro
  (assume h hp ha, h ⟨hp, ha⟩)
  (assume h ⟨hp, ha⟩, h hp ha)

lemma and_exists {α : Sort*} {p : α → Prop} {a : Prop} :
  (a ∧ (∃x, p x)) ↔ (∃x, a ∧ p x) :=
iff.intro
  (assume ⟨ha, x, hp⟩, ⟨x, ha, hp⟩)
  (assume ⟨x, ha, hp⟩, ⟨ha, x, hp⟩)

@[simp] lemma exists_false {α : Sort*} :
  (∃x : α, false) ↔ false :=
iff.intro (assume ⟨a, f⟩, f) (assume h, h.elim)


/-! ## Natural Numbers -/

attribute [simp] nat.add


/-! ## Integers -/

@[simp] lemma int.neg_comp_neg :
  int.neg ∘ int.neg = id :=
begin
  apply funext,
  apply neg_neg
end


/-! ## Reflexive Transitive Closure -/

namespace rtc

inductive star {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c

attribute [refl] star.refl

namespace star

variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

@[trans] lemma trans (hab : star r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    assumption },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma single (hab : r a b) :
  star r a b :=
refl.tail hab

lemma head (hab : r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    exact (tail refl) hab },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma head_induction_on {α : Sort*} {r : α → α → Prop} {b : α}
  {P : ∀a : α, star r a b → Prop} {a : α} (h : star r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : star r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction' h,
  case star.refl {
    exact refl },
  case star.tail : b c hab hbc ih {
    apply ih,
    show P b _, from
      head hbc _ refl,
    show ∀a a', r a a' → star r a' b → P a' _ → P a _, from
      assume a a' hab hbc, head hab _ }
end

lemma trans_induction_on {α : Sort*} {r : α → α → Prop}
    {p : ∀{a b : α}, star r a b → Prop} {a b : α} (h : star r a b)
    (ih₁ : ∀a, @p a a refl) (ih₂ : ∀{a b} (h : r a b), p (single h))
    (ih₃ : ∀{a b c} (h₁ : star r a b) (h₂ : star r b c), p h₁ →
       p h₂ → p (h₁.trans h₂)) :
  p h :=
begin
  induction' h,
  case star.refl {
    exact ih₁ a },
  case star.tail : b c hab hbc ih {
    exact ih₃ hab (single hbc) (ih ih₁ @ih₂ @ih₃) (ih₂ hbc) }
end

lemma lift {β : Sort*} {s : β → β → Prop} (f : α → β)
  (h : ∀a b, r a b → s (f a) (f b)) (hab : star r a b) :
  star s (f a) (f b) :=
hab.trans_induction_on
  (assume a, refl)
  (assume a b, single ∘ h _ _)
  (assume a b c _ _, trans)

lemma mono {p : α → α → Prop} :
  (∀a b, r a b → p a b) → star r a b → star p a b :=
lift id

lemma star_star_eq :
  star (star r) = star r :=
funext
  (assume a,
   funext
     (assume b,
      propext (iff.intro
        (assume h,
         begin
           induction' h,
           { refl },
           { transitivity;
               assumption }
         end)
        (star.mono (assume a b,
           single)))))

end star

end rtc

export rtc


/-! ## States -/

def state :=
string → ℕ

def state.update (name : string) (val : ℕ) (s : state) : state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

instance : has_emptyc state :=
{ emptyc := λ_, 0 }

@[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} name = val :=
if_pos rfl

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
    (h : name' ≠ name . tactic.dec_trivial) :
  s{name ↦ val} name' = s name' :=
if_neg h

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

example (s : state) :
  s{"a" ↦ 0}{"a" ↦ 2} = s{"a" ↦ 2} :=
by simp

example (s : state) :
  s{"a" ↦ 0}{"b" ↦ 2} = s{"b" ↦ 2}{"a" ↦ 0} :=
by simp

example (s : state) :
  s{"a" ↦ s "a"}{"b" ↦ 0} = s{"b" ↦ 0} :=
by simp


/-! ## Relations -/

def Id {α : Type} : set (α × α) :=
{ab | prod.snd ab = prod.fst ab}

@[simp] lemma mem_Id {α : Type} (a b : α) :
  (a, b) ∈ @Id α ↔ b = a :=
by refl

def comp {α : Type} (r₁ r₂ : set (α × α)) : set (α × α) :=
{ac | ∃b, (prod.fst ac, b) ∈ r₁ ∧ (b, prod.snd ac) ∈ r₂}

infixl ` ◯ ` : 90 := comp

@[simp] lemma mem_comp {α : Type} (r₁ r₂ : set (α × α))
    (a b : α) :
  (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
by refl

def restrict {α : Type} (r : set (α × α)) (p : α → Prop) :
  set (α × α) :=
{ab | p (prod.fst ab) ∧ ab ∈ r}

infixl ` ⇃ ` : 90 := restrict

@[simp] lemma mem_restrict {α : Type} (r : set (α × α))
    (p : α → Prop) (a b : α) :
  (a, b) ∈ r ⇃ p ↔ p a ∧ (a, b) ∈ r :=
by refl

end LoVe
