import .lovelib


/- # LoVe Homework 7: Metaprogramming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (9 points): A `mindless` Tactic

We develop a tactic that automates some of the mindless `intro`/`apply`
proofs that formed the core of lecture 2.

We proceed in three steps.

1.1 (6 points). Develop a `mindless_safe` tactic that applies the
introduction rules for `true`, `∧`, and `↔`, that applies `tactic.intro` (or
`tactic.intro1`) for `→`/`∀`, and that applies `tactic.assumption`, repeatedly
on all goals. The tactic generalizes `intro_ands` from the exercise.

Hint: You can use the `<|>` operator between the rules/tactics used for
different symbols. -/

meta def mindless_safe : tactic unit :=
do
  tactic.repeat (
    tactic.applyc ``true.intro
    <|> tactic.applyc ``and.intro
    <|> tactic.applyc ``iff.intro
    <|> tactic.intro1 >> pure ()
    <|> tactic.assumption
  )

lemma abcd (a b c d : Prop) (hc : c) :
  a → ¬ b ∧ (c ↔ d) :=
begin
  mindless_safe,
  /- The proof state should be roughly as follows:

  a b c d : Prop,
  hc : c,
  a_1 : a,
  a_2 : b
  ⊢ false

  a b c d : Prop,
  hc : c,
  a_1 : a,
  a_2 : c
  ⊢ d -/
  repeat { sorry }
end

/- 1.2 (3 points). Develop a `mindless_unsafe` tactic that works on the current
goal. It first tries to apply each hypothesis in turn using `tactic.apply`, then
invokes some `continue` tactic, which is passed as argument, and finally checks
that this succeeded by invoking `tactic.done` (which succeeds only if there are
no goals left). -/

meta def mindless_unsafe (continue : tactic unit) : tactic unit :=
do
  ctx ← tactic.local_context,
  mmap (λ h, do {
    tactic.all_goals (tactic.try (tactic.apply h))
  }) ctx,
  continue,
  tactic.done

lemma modus_ponens (a b : Prop) (ha : a) (hab : a → b) :
  b :=
by mindless_unsafe tactic.assumption

/- Finally, everything comes together with the `mindless` tactic below. The
tactic performs a depth-bounded search for a proof, applying `mindless_safe`
and `mindless_unsafe` on all goals in alternation. The bound is necessary to
eventually backtrack. -/

meta def mindless : ℕ → tactic unit
| 0           :=
  do
    tactic.all_goals (tactic.try mindless_safe),
    pure ()
| (depth + 1) :=
  do
    tactic.all_goals (tactic.try mindless_safe),
    tactic.all_goals (tactic.try (mindless_unsafe (mindless depth))),
    pure ()

/- Some tests are provided below. All should succeed. -/

lemma I (a : Prop) :
  a → a :=
by mindless 0

lemma K (a b : Prop) :
  a → b → b :=
by mindless 0

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
by mindless 1

lemma proj_1st (a : Prop) :
  a → a → a :=
by mindless 0

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
by mindless 1

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
by mindless 2

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
by mindless 2

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
by mindless 2

lemma more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
by mindless 1

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
by mindless 1

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
by mindless 3

lemma one_for_the_road (a c : Prop) (ha : a) (hccc : c → c → c) (haac : a → c) :
  c :=
by mindless 1


/- ## Question 2 (2 bonus points): An `auto` Tactic

2.1 (1 bonus point). Develop an Isabelle-style `auto` tactic.

This tactic would apply all harmless introduction and elimination rules. In
addition, it would try potentially harmful rules (such as `or.intro_left` and
`false.elim`) but backtrack at some point (or try several possibilities in
parallel). Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also attempt to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

See also "Automatic Proof and Disproof in Isabelle/HOL"
(https://www.cs.vu.nl/~jbe248/frocos2011-dis-proof.pdf) by Blanchette, Bulwahn,
and Nipkow, and the references they give. -/

/- a very dumb automatic tactic using breadth-first search -/
meta def auto_dfs (max_goals : ℕ): list tactic_state → tactic unit
| []        := tactic.fail "dead end reached"
| (s :: ss) :=
  do
    -- set tactic state to the one at the head of the list
    tactic.write s,
    -- apply some harmless tactics to all goals
    tactic.repeat (
      tactic.intro1 >> pure ()
      <|> tactic.assumption
    ),
    tactic.done <|> do {
      s ← tactic.read,
      ctx ← tactic.local_context,
      let rules := [
        ``true.intro,
        ``false.elim,
        ``and.intro,
        ``and.elim_left,
        ``and.elim_right,
        ``or.intro_left,
        ``or.intro_right,
        ``or.elim,
        ``iff.intro,
        ``iff.elim,
        ``exists.intro,
        ``exists.elim
      ],
      -- list of tactics representing the application of assumptions and rules
      let tactics :=
        list.map (λ h, tactic.apply h >> pure ()) ctx
        ++ list.map tactic.applyc rules,
      ss ← monad.foldl (λ ss t, do {
        tactic.write s,
        t, -- try to apply tactic
        goals ← tactic.get_goals,
        if goals.length > max_goals then
          tactic.fail "too many goals"
        else do {
          s ← tactic.read,
          /- If tactic applies and does not create too many goals, append the
          state after application to the list of states to process. -/
          pure (ss ++ [s])
        }
      /- If tactic does not apply or creates too many goals, do not modify list
      of states to process. -/
      } <|> pure ss) ss tactics,
      auto_dfs ss
    }

meta def auto (max_goals : ℕ) : tactic unit :=
do
  s ← tactic.read,
  -- at first, there is only one tactic state to process
  auto_dfs max_goals [s]

/- 2.2 (1 bonus point). Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise 2
and homework 2. Please include these below. -/

lemma i (a : Prop) :
  a → a :=
by auto 1

lemma ii (a b c : Prop) :
  (a → b → c) → b → a → c :=
by auto 2

lemma iii (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
by auto 1

lemma iv (a b : Prop) :
  ¬ a ∨ b → a → b :=
by auto 5

lemma v {α : Type} (p : α → Prop) :
  (∃ x, p x) → (∃ x, p x) :=
by auto 1

lemma vi (a b : Prop) :
  a ∨ b → ¬ a → b :=
by auto 5

lemma vii (a b : Prop) :
  (a → b) → (¬b → ¬a) :=
by auto 1

lemma viii (a b : Prop) :
  (a ∨ b) → (a → b) → ¬b → b :=
by auto 5

lemma ix (a b c : Prop) :
  ((a ∧ b) → c) ↔ (a → b → c) :=
by auto 3

/- For more complex examples, the tactic needs to be smarter at fighting
exponentional growth of the number of states to process. -/

end LoVe
