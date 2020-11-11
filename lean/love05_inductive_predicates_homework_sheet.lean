import .lovelib


/- # LoVe Homework 5: Inductive Predicates

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (3 points): A Type of λ-Terms

Recall the following type of λ-terms from question 3 of exercise 4. -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/- 1.1 (1 point). Define an inductive predicate `is_app` that returns true if
and only if its argument has an `app` constructor at the top level. -/

inductive is_app : term → Prop
| app {t u : term} : is_app (term.app t u)

lemma is_app_iff_is_app (s : term) :
  is_app s ↔ ∃ t u : term, s = term.app t u :=
begin
  apply iff.intro,
  {
    intro h,
    cases' s,
    case var {
      apply false.elim,
      cases' h,
    },
    case lam {
      apply false.elim,
      cases' h,
    },
    case app : t u {
      apply exists.intro t,
      apply exists.intro u,
      refl,
    },
  }, {
    intro h,
    apply exists.elim h,
    intro s,
    intro h,
    apply exists.elim h,
    intro u,
    intro _,
    simp [*],
    apply is_app.app,
  },
end

/- 1.2 (2 points). Define an inductive predicate `is_abs_free` that is true if
and only if its argument is a λ-term that contains no λ-expressions. -/

inductive is_abs_free : term → Prop
| var {x : string} : is_abs_free (term.var x)
| app {t u : term} : is_abs_free t → is_abs_free u → is_abs_free (term.app t u)

lemma lam_is_not_abs_free {x : string} {t : term} :
  ¬is_abs_free (term.lam x t) :=
begin
  intro h,
  cases' h,
end

lemma xy_is_abs_free {x y : string} :
  is_abs_free (term.app (term.var x) (term.var y)) :=
begin
  apply is_abs_free.app,
  apply is_abs_free.var,
  apply is_abs_free.var,
end

/- ## Question 2 (6 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive even : ℕ → Prop
| zero            : even 0
| add_two {n : ℕ} : even n → even (n + 2)

/- 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `even`,
and should not rely on `even`. -/

inductive odd : ℕ → Prop
| one             : odd 1
| add_two {n : ℕ} : odd n → odd (n + 2)

/- 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

lemma odd_3 :
  odd 3 :=
odd.add_two odd.one

lemma odd_5 :
  odd 5 :=
odd.add_two (odd.add_two odd.one)

/- 2.3 (2 points). Prove the following lemma by rule induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how rule
induction works (and is good practice for the final exam).

    lemma even_odd {n : ℕ} (heven : even n) :
      odd (n + 1) :=

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

/- We perform the proof by structural induction on `heven`.

Case `zero`: The goal is `odd (0 + 1)`.
By `linarith`, we have `0 + 1 = 1`. By `odd.one`, we have `odd 1`.
We conclude `odd (0 + 1)`.

Case `add_two`: The goal is `odd (n + 2 + 1)`.
The induction hypothesis is `odd (n + 1)`.
By `odd.add_two` and the induction hypothesis, we have `odd (n + 1 + 2)`.
By `linarith`, we have `n + 1 + 2 = n + 2 + 1`.
We conclude `odd (n + 2 + 1)`. -/

/- 2.4 (1 point). Prove the same lemma again, but this time in Lean: -/

lemma even_odd {n : ℕ} (heven : even n) :
  odd (n + 1) :=
begin
  induction' heven,
  case zero {
    exact odd.one,
  },
  case add_two {
    apply odd.add_two,
    exact ih,
  },
end

/- 2.5 (1 point). Prove the following lemma in Lean.

Hint: Recall that `¬ a` is defined as `a → false`. -/

lemma even_not_odd {n : ℕ} (heven : even n) :
  ¬ odd n :=
begin
  intro hodd,
  induction' heven,
  case zero {
    cases' hodd,
  },
  case add_two {
    apply ih,
    cases' hodd,
    exact hodd,
  },
end

end LoVe
