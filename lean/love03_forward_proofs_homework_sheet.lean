import .love02_backward_proofs_exercise_sheet


/- # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (6 points + 1 bonus point): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
assume dn,
show _, from peirce_of_em (sorry_lemmas.em_of_dn dn)

lemma em_of_peirce :
  peirce → excluded_middle :=
assume p,
show _, from sorry_lemmas.em_of_dn (dn_of_peirce p)

lemma dn_of_em :
  excluded_middle → double_negation :=
assume em,
show _, from dn_of_peirce (peirce_of_em em)

end backward_proofs

/- 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
show _, from iff.intro (
  assume hex,
  show _, from exists.elim hex (
    fix x,
    assume hpq : p x ∧ q x,
    have qp : _ := and.intro (and.elim_right hpq) (and.elim_left hpq),
    show _, from exists.intro x qp
  )
) (
  assume hex,
  show _, from exists.elim hex (
    fix x,
    assume hqp : q x ∧ p x,
    have pq : _ := and.intro (and.elim_right hqp) (and.elim_left hqp),
    show _, from exists.intro x pq
  )
)

/- 1.3 (1 bonus point). Supply a structured proof of the following property,
which can be used pull a `∀`-quantifier past an `∃`-quantifier. -/

lemma forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
assume hex,
fix y,
show _, from exists.elim hex (
  fix x,
  assume hall,
  have pxy : _ := hall y,
  show _, from exists.intro x pxy
)


/- ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied "Logic and Sets" with Prof. Fokkink, you will know he is
very fond of logic puzzles. This question is meant as a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/- 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
λ a b habaab, habaab (λ habaa, habaa (λ ha, habaab (λ haba, ha)))

/- 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
fix a b,
assume habaab,
show b, from habaab (
  assume haba,
  show a, from haba (
    assume ha,
    show b, from habaab (
      assume haba,
      show a, from ha
    )
  )
)

end LoVe
