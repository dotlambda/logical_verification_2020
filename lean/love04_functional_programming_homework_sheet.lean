import .love04_functional_programming_demo


/- # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (2 points): Maps

1.1 (1 point). Complete the following definition. The `map_btree` function
should apply its argument `f` to all values of type `α` stored in the tree and
otherwise preserve the tree's structure. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node (f a) (map_btree l) (map_btree r)

/- 1.2 (1 point). Prove the following lemma about your `map_btree` function. -/

lemma map_btree_iden {α : Type} :
  ∀t : btree α, map_btree (λa, a) t = t
| btree.empty        := by refl
| (btree.node a l r) := by simp [map_btree, map_btree_iden l, map_btree_iden r]


/- ## Question 2 (4 points): Tail-Recursive Factorials -/

/- Recall the definition of the factorial functions -/

#check fact

/- 2.1 (2 points). Experienced functional programmers tend to avoid definitions
such as the above, because they lead to a deep call stack. Tail recursion can be
used to avoid this. Results are accumulated in an argument and returned. This
can be optimized by compilers. For factorials, this gives the following
definition: -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

/- Prove that, given 1 as the accumulator `a`, `accufact` computes `fact`.

Hint: You will need to prove a generalized version of the statement as a
separate lemma or `have`, because the desired propery fixes `a` to 1, which
yields a too weak induction hypothesis. -/

lemma accufact_fact :
  ∀ a n : ℕ, accufact a n = a * fact n
| a 0       := by simp [accufact, fact]
| a (n + 1) :=
  begin
    simp [accufact, fact],
    simp [accufact_fact _ n],
    cc,
  end

lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = fact n :=
by simp [accufact_fact 1 n]

/- 2.2 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

/- We show `∀ n a, accufact a n = a * fact n` by induction on `n`.

Case `0`: Let `a : ℕ`. The goal is `accufact a 0 = a * fact 0`.
We have
    `accufact a 0 = a` by definition of `accufact`
                 `= a * 1` by `mul_one`
                 `= a * fact 0` by definition of `fact`.

Case `n + 1`: The induction hypothesis is `∀ a, accufact a n = a * fact n`.
Let `a : ℕ`. The goal is `accufact a (n + 1) = a * fact (n + 1)`.
We have
    `accufact a (n + 1) = accufact ((n + 1) * a) n` by definition of `accufact`
                       `= ((n + 1) * a) * fact n` by the induction hypothesis
                       `= (a * (n + 1)) * fact n` by commutativity of `*`
                       `= a * ((n + 1) * fact n)` by associativity of `*`
                       `= a * fact (n + 1)` by definition of `fact`.

We conclude `∀ a n, accufact a n = a * fact n` from the above using
commutativity of uiversal quantifiers. Hence
    `∀ n, accufact 1 n = 1 * fact n` as an instance of the above
                      `= fact n` by `one_mul`. -/


/- ## Question 3 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/- 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1)
| 0       := by refl
| (m + 1) :=
  calc  2 * sum_upto (λ i, i) (m + 1)
      = 2 * sum_upto (λ i, i) m + 2 * (m + 1) :
    by simp [sum_upto, mul_add]
  ... = m * (m + 1) + 2 * (m + 1) :
    by simp [sum_upto_eq m]
  ... = (m + 2) * (m + 1) :
    by simp [add_mul]
  ... = (m + 1) * (m + 1 + 1) :
    by simp [mul_comm]

/- 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n
| 0       := by refl
| (m + 1) :=
  begin
    simp [sum_upto],
    simp [add_assoc, sum_upto_mul m],
    cc
  end

end LoVe
