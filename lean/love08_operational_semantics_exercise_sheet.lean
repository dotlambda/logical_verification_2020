import .love08_operational_semantics_demo


/- # LoVe Exercise 8: Operational Semantics -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ≈ S₂`. -/

def big_step_equiv (S₁ S₂ : stmt) : Prop :=
∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix ` ≈ ` := big_step_equiv

/- Program equivalence is a equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

@[refl] lemma big_step_equiv.refl {S : stmt} :
  S ≈ S :=
fix s t,
show (S, s) ⟹ t ↔ (S, s) ⟹ t, from
  by refl

@[symm] lemma big_step_equiv.symm {S₁ S₂ : stmt}:
  S₁ ≈ S₂ → S₂ ≈ S₁ :=
assume h : S₁ ≈ S₂,
fix s t,
show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t, from
  iff.symm (h s t)

@[trans] lemma big_step_equiv.trans {S₁ S₂ S₃ : stmt} (h₁₂ : S₁ ≈ S₂)
    (h₂₃ : S₂ ≈ S₃) :
  S₁ ≈ S₃ :=
fix s t,
show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t, from
  iff.trans (h₁₂ s t) (h₂₃ s t)


/- 1.1. Prove the following program equivalences. -/

lemma big_step_equiv.skip_assign_id {x} :
  stmt.assign x (λs, s x) ≈ stmt.skip :=
begin
  intros s t,
  rw big_step_assign_iff,
  rw big_step_skip_iff,
  rw update_id,
end

lemma big_step_equiv.seq_skip_left {S : stmt} :
  stmt.skip ;; S ≈ S :=
begin
  intros s t,
  rw big_step_seq_iff,
  apply iff.intro,
  {
    intro h,
    apply exists.elim h,
    intros r h,
    rw big_step_skip_iff at h,
    rw ←(and.elim_left h),
    exact and.elim_right h,
  },
  {
    intro h,
    apply exists.intro s,
    apply and.intro big_step.skip h,
  },
end

lemma big_step_equiv.seq_skip_right {S : stmt} :
  S ;; stmt.skip ≈ S :=
begin
  intros s t,
  simp,
end

lemma big_step_equiv.ite_seq_while {b} {S : stmt} :
  stmt.ite b (S ;; stmt.while b S) stmt.skip ≈ stmt.while b S :=
begin
  intros s t,
  rw big_step_while_iff,
  simp,
end

/- 1.2. Program equivalence can be used to replace subprograms by other
subprograms with the same semantics. Prove the following so-called congruence
rules: -/

lemma big_step_equiv.seq_congr {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  S₁ ;; T₁ ≈ S₂ ;; T₂ :=
begin
  intros s t,
  apply iff.intro,
  {
    intro h,
    simp at h,
    apply exists.elim h,
    intros r h,
    rw hS at h,
    rw hT at h,
    exact big_step.seq (and.elim_left h) (and.elim_right h),
  },
  {
    intro h,
    simp at h,
    apply exists.elim h,
    intros r h,
    rw ←hS at h,
    rw ←hT at h,
    exact big_step.seq (and.elim_left h) (and.elim_right h),
  },
end

lemma big_step_equiv.ite_congr {b} {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  stmt.ite b S₁ T₁ ≈ stmt.ite b S₂ T₂ :=
begin
  intros s t,
  apply iff.intro,
  repeat {
    simp only [big_step_ite_iff],
    rw hS,
    rw hT,
    intro h,
    exact h,
  },
end

/- 1.3 (**optional**): Prove one more congruence rule. This one is more
difficult. -/

lemma denote_equiv.while_congr {b} {S₁ S₂ : stmt} (hS : S₁ ≈ S₂) :
  stmt.while b S₁ ≈ stmt.while b S₂ :=
begin
  intros s t,
  apply iff.intro,
  repeat {
    intro h,
    induction' h,
    case while_true : b S₁ s t u hb hS' hw ihS ihw {
      rw big_step_while_iff,
      apply or.intro_left,
      apply exists.intro t,
      rw ←hS <|> rw hS,
      simp *,
    },
    case while_false : b S₁ s hnb {
      apply big_step.while_false hnb,
    },
  },
end


/- ## Question 2: Guarded Command Language (GCL)

In 1976, E. W. Dijkstra introduced the guarded command language, a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert b     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert b` aborts if `b` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace gcl

inductive stmt (σ : Type) : Type
| assign : string → (σ → ℕ) → stmt
| assert : (σ → Prop) → stmt
| seq    : stmt → stmt → stmt
| choice : list stmt → stmt
| loop   : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/- The parameter `σ` abstracts over the state type. It is necessary as a work
around for a Lean bug.

The big-step semantics is defined as follows: -/

inductive big_step : (stmt state × state) → state → Prop
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| assert {b : state → Prop} {s} (hcond : b s) :
  big_step (stmt.assert b, s) s
| seq {S T s t u} (h₁ : big_step (S, s) t) (h₂ : big_step (T, t) u) :
  big_step (S ;; T, s) u
| choice {Ss s t} (i) (hless : i < list.length Ss)
    (hbody : big_step (list.nth_le Ss i hless, s) t) :
  big_step (stmt.choice Ss, s) t
| loop_base {S s} :
  big_step (stmt.loop S, s) s
| loop_step {S s u} (t) (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.loop S, t) u) :
  big_step (stmt.loop S, s) u

infix ` ⟹ ` : 110 := big_step

/- 2.1. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] lemma big_step_assign_iff {x a s t} :
  (stmt.assign x a, s) ⟹ t ↔ t = s{x ↦ a s} :=
begin
  apply iff.intro,
  {
    intro h,
    cases' h,
    refl,
  },
  {
    intro h,
    rw h,
    exact big_step.assign,
  }
end

@[simp] lemma big_step_assert {b s t} :
  (stmt.assert b, s) ⟹ t ↔ t = s ∧ b s :=
begin
  apply iff.intro,
  {
    intro h,
    cases' h,
    simp *,
  },
  {
    intro h,
    rw (and.elim_left h),
    apply big_step.assert (and.elim_right h),
  },
end

@[simp] lemma big_step_seq_iff {S₁ S₂ s t} :
  (stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
begin
  apply iff.intro,
  {
    intro h,
    cases' h,
    apply exists.intro,
    apply and.intro,
    assumption,
    assumption,
  },
  {
    intro h,
    apply exists.elim h,
    intros u h,
    exact big_step.seq (and.elim_left h) (and.elim_right h),
  },
end

lemma big_step_loop {S s u} :
  (stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (stmt.loop S, t) ⟹ u)) :=
begin
  apply iff.intro,
  {
    intro h,
    cases' h,
    case loop_base {
      apply or.intro_left,
      refl,
    },
    case loop_step {
      apply or.intro_right,
      apply exists.intro,
      apply and.intro,
      assumption,
      assumption,
    },
  },
  {
    intro h,
    apply or.elim h,
    {
      intro h,
      rw ←h,
      exact big_step.loop_base,
    },
    {
      intro h,
      apply exists.elim h,
      intros t h,
      apply big_step.loop_step,
      exact and.elim_left h,
      exact and.elim_right h,
    }
  }
end

@[simp] lemma big_step_choice {Ss s t} :
  (stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < list.length Ss),
     (list.nth_le Ss i hless, s) ⟹ t) :=
begin
  apply iff.intro,
  {
    intro h,
    cases' h,
    apply exists.intro,
    apply exists.intro,
    assumption,
  },
  {
    intro h,
    apply exists.elim h,
    intros i h,
    apply exists.elim h,
    intros hless h,
    apply big_step.choice i hless h,
  }
end

end gcl

/- 2.2. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : stmt → gcl.stmt state
| stmt.skip         := gcl.stmt.assert (λ_, true)
| (stmt.assign x a) :=
  gcl.stmt.assign x a
| (S ;; T)          :=
  gcl_of S ;; gcl_of T
| (stmt.ite b S T)  :=
  gcl.stmt.choice [
    gcl.stmt.assert (λ s, b s) ;; gcl_of S,
    gcl.stmt.assert (λ s, ¬b s) ;; gcl_of T
  ]
| (stmt.while b S)  :=
  gcl.stmt.loop (gcl.stmt.assert b ;; gcl_of S) ;; gcl.stmt.assert (λ s, ¬b s)

/- 2.3. In the definition of `gcl_of` above, `skip` is translated to
`assert (λ_, true)`. Looking at the big-step semantics of both constructs, we
can convince ourselves that it makes sense. Can you think of other correct ways
to define the `skip` case? -/

-- `gcl.stmt.loop (gcl.stmt.assert (λ _, false))`

end LoVe
