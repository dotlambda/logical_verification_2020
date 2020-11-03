import .lovelib


/- # LoVe Exercise 3: Forward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha,
show a, from
  ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha hb,
show b, from
  hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume habc hb ha,
show c, from
  habc ha hb

lemma proj_1st (a : Prop) :
  a → a → a :=
assume ha ha',
show a, from
  ha

/- Please give a different answer than for `proj_1st`. -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
assume ha ha',
show a, from
  ha'

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume habc ha hac hb,
show c, from
  hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume hab hnb ha,
show false, from
  not.elim hnb (hab ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
iff.intro (
  assume hall,
  show _, from
    and.intro (
      fix x,
      have pxqx : _ := hall x,
      show _, from
        and.elim_left pxqx
    ) (
      fix x,
      have pxqx : _ := hall x,
      show _, from
        and.elim_right pxqx
    )
) (
  assume hand,
  have hallp : _ := and.elim_left hand,
  have hallq : _ := and.elim_right hand,
  fix x,
  have px : _ := hallp x,
  have qx : _ := hallq x,
  show _, from
    and.intro px qx
)

/- 1.4. Reuse, if possible, the lemma `forall_and` you proved above to prove
the following instance of the lemma. -/

lemma forall_and_inst {α : Type} (r s : α → α → Prop) :
  (∀x, r x x ∧ s x x) ↔ (∀x, r x x) ∧ (∀x, s x x) :=
forall_and (λ x, r x x) (λ x, s x x)


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      `(a + b) * (a + b)`
    `= a * (a + b) + b * (a + b)`
    `= a * a + a * b + b * a + b * b`
    `= a * a + a * b + a * b + b * b`
    `= a * a + 2 * a * b + b * b`

Hint: You might need the tactics `simp` and `cc` and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
calc  (a + b) * (a + b)
    = a * (a + b) + b * (a + b) :
  by rw add_mul
... = a * a + a * b + (b * a + b * b) :
  by simp [mul_add]
... = a * a + (a * b + a * b) + b * b :
  by cc
... = a * a + (a + a) * b + b * b :
  by rw add_mul
... = a * a + 2 * a * b + b * b :
  by rw two_mul

/- 2.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
have (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
  by rw add_mul,
have a * (a + b) + b * (a + b) = a * a + a * b + (b * a + b * b) :=
  by simp [mul_add],
have a * a + (a * b + a * b) + b * b = a * a + (a + a) * b + b * b :=
  by rw add_mul,
have a * a + (a + a) * b + b * b = a * a + 2 * a * b + b * b :=
  by rw two_mul,
show _, from
  by cc

/- 2.3. Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  simp [mul_add, add_mul, two_mul],
  cc,
end


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom forall.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∀x : α, x = t ∧ p x) ↔ p t

def is_zero (n : ℕ) :=
  n = 0

lemma proof_of_false :
  false :=
have p0 : is_zero 0 := by simp [is_zero],
have hall : _ := iff.elim_right forall.one_point_wrong p0,
have h10 : _ := and.elim_left (hall 1),
show false, by cc

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a tactical or structured proof. -/

axiom exists.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t → p x) ↔ p t

lemma proof_of_false₂ :
  false :=
begin
  have h : is_zero 1 → false := by simp [is_zero],
  apply h,
  apply iff.elim_left (@exists.one_point_wrong ℕ 1 is_zero),
  apply exists.intro 0,
  assume _,
  simp [is_zero],
end

end LoVe
