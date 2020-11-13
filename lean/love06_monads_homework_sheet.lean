import .love06_monads_demo


/- # LoVe Homework 6: Monads

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (6 points): Better Exceptions

The __error monad__ is a monad stores either a value of type `α` or an error of
type `ε`. This corresponds to the following type: -/

inductive error (ε α : Type) : Type
| good {} : α → error
| bad {}  : ε → error

def error.repr {ε α : Type} [has_repr ε] [has_repr α] :
  error ε α → string
| (error.good a) := "error.good " ++ repr a
| (error.bad e)  := "error.bad " ++ repr e

@[instance] def error.has_repr {ε α : Type} [has_repr ε] [has_repr α] :
  has_repr (error ε α) :=
{ repr := error.repr }

/- The error monad generalizes the option monad seen in the lecture. The `good`
constructor, corresponding to `option.some`, stores the current result of the
computation. But instead of having a single bad state `option.none`, the error
monad has many bad states of the form `bad e`, where `e` is an "exception" of
type `ε`.

1.1 (1 point). Implement a variant of `list.nth` that returns an error
message of the form "index _i_ out of range" instead of `option.none` on
failure.

Hint: For this, you will only need pattern matching (no monadic code). -/

#check list.nth

def list.nth_error {α : Type} (as : list α) (i : ℕ) : error string α :=
match list.nth as i with
| option.some a := error.good a
| option.none   := error.bad ("index " ++ to_string i ++ " out of range")
end

#eval list.nth_error [0, 1, 2, 3] 4

/- 1.2 (1 point). Complete the definitions of the `pure` and `bind` operations
on the error monad: -/

def error.pure {ε α : Type} : α → error ε α :=
λ a, error.good a

def error.bind {ε α β : Type} : error ε α → (α → error ε β) → error ε β
| (error.good a) f :=
  match f a with
  | error.good b := error.good b
  | error.bad e  := error.bad e
  end
| (error.bad e)  _ := error.bad e

/- The following type class instance makes it possible to use `>>=` and `do`
notations in conjunction with error monads: -/

@[instance] def error.monad {ε : Type} : monad (error ε) :=
{ pure := @error.pure ε,
  bind := @error.bind ε }

/- 1.3 (2 point). Prove the monad laws for the error monad. -/

lemma error.pure_bind {ε α β : Type} (a : α) (f : α → error ε β) :
  (pure a >>= f) = f a :=
begin
  simp [(>>=), pure, error.pure, error.bind],
  cases' f a,
  case error.good {
    refl,
  },
  case error.bad {
    refl,
  },
end

lemma error.bind_pure {ε α : Type} (ma : error ε α) :
  (ma >>= pure) = ma :=
begin
  cases' ma,
  case error.good {
    refl,
  },
  case error.bad {
    refl,
  },
end

lemma error.bind_assoc {ε α β γ : Type} (f : α → error ε β) (g : β → error ε γ)
    (ma : error ε α) :
  ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)) :=
begin
  cases' ma,
  case error.good : a {
    simp [(>>=), error.bind],
    cases' f a,
    case error.good : b {
      simp [error.bind],
      cases' g b,
      case error.good {
        refl,
      },
      case error.bad {
        refl,
      },
    },
    case error.bad {
      refl,
    },
  },
  case error.bad {
    refl,
  },
end

/- 1.4 (1 point). Define the following two operations on the error monad.

The `throw` operation raises an exception `e`, leaving the monad in a bad state
storing `e`.

The `catch` operation can be used to recover from an earlier exception. If the
monad is currently in a bad state storing `e`, `catch` invokes some
exception-handling code (the second argument to `catch`), passing `e` as
argument; this code might in turn raise a new exception. If `catch` is applied
to a good state, nothing happens—the monad remains in the good state. As a
convenient alternative to `error.catch ma g`, Lean lets us write
`ma.catch g`. -/

def error.throw {ε α : Type} : ε → error ε α :=
λ e, error.bad e

def error.catch {ε α : Type} : error ε α → (ε → error ε α) → error ε α
| (error.good a) _ := error.good a
| (error.bad e)  f := f e

/- 1.5 (1 point). Using `list.nth_error` and the monadic operations on `error`,
and the special `error.catch` operation, write a monadic program that swaps the
values at indexes `i` and `j` in the input list `as`. If either of the indices
is out of range, return `as` unchanged. -/

def change_at_index {α : Type} (index : ℕ) (element : α) :
  ℕ → list α → list α
| _ []        := []
| i (a :: as) :=
  if i = index then
    element :: as
  else
    a :: change_at_index (i + 1) as

def list.swap {α : Type} (as : list α) (i j : ℕ) : error string (list α) :=
do {
  ai ← list.nth_error as i,
  aj ← list.nth_error as j,
  pure (change_at_index i aj 0 (change_at_index j ai 0 as))
}.catch (λ _, pure as)

def list.swap' {α : Type} (as : list α) (i j : ℕ) : error string (list α) :=
error.catch (do
  ai ← list.nth_error as i,
  aj ← list.nth_error as j,
  if i < j then
    pure (as.take i ++ [aj] ++ list.take (j - i - 1) (as.drop (i + 1)) ++ [ai] ++ as.drop (j + 1))
  else if j < i then
    pure (as.take j ++ [ai] ++ list.take (i - j - 1) (as.drop (j + 1)) ++ [aj] ++ as.drop (i + 1))
  else
    pure as
) (λ _, pure as)

#reduce list.swap [3, 1, 4, 1] 0 2   -- expected: error.good [4, 1, 3, 1]
#reduce list.swap [3, 1, 4, 1] 2 0   -- expected: error.good [4, 1, 3, 1]
#reduce list.swap [3, 1, 4, 1] 0 7   -- expected: error.good [3, 1, 4, 1]
#reduce list.swap [3, 1, 4, 1] 0 0   -- expected: error.good [3, 1, 4, 1]


/- ## Question 2 (3 points + 1 bonus point): Properties of `mmap`

We will prove some properties of the `mmap` function introduced in the
lecture's demo. -/

#check mmap

/- 2.1 (1 point). Prove the following identity law about `mmap` for an
arbitrary monad `m`.

Hint: You will need the lemma `lawful_monad.pure_bind` in the induction step. -/

lemma mmap_pure {m : Type → Type} [lawful_monad m] {α : Type} (as : list α) :
  mmap (@pure m _ _) as = pure as :=
begin
  induction' as,
  case nil {
    refl,
  },
  case cons : a as {
    simp [mmap, lawful_monad.pure_bind, ih],
  },
end

/- Commutative monads are monads for which we can reorder actions that do not
depend on each others. Formally: -/

@[class] structure comm_lawful_monad (m : Type → Type)
  extends lawful_monad m : Type 1 :=
(bind_comm {α β γ δ : Type} (ma : m α) (f : α → m β) (g : α → m γ)
     (h : α → β → γ → m δ) :
   (ma >>= (λa, f a >>= (λb, g a >>= (λc, h a b c)))) =
   (ma >>= (λa, g a >>= (λc, f a >>= (λb, h a b c)))))

/- 2.2 (1 point). Prove that `option` is a commutative monad. -/

lemma option.bind_comm {α β γ δ : Type} (ma : option α) (f : α → option β)
    (g : α → option γ) (h : α → β → γ → option δ) :
  (ma >>= λa, f a >>= λb, g a >>= λc, h a b c) =
  (ma >>= λa, g a >>= λc, f a >>= λb, h a b c) :=
begin
  cases' ma,
  case none {
    refl,
  },
  case some : a {
    simp [(>>=), option.bind],
    cases' f a,
    case none {
      simp [option.bind],
      cases' g a,
      refl,
      refl,
    },
    case some : b {
      refl,
    },
  },
end

/- 2.3 (1 point). Explain why `error` is not a commutative monad. -/

/- Since `error` "stops execution" after an `error.bad` occurs, only the
exception of the first function that fails is returned. Hence the order in
which those functions are executed matters. For example, -/
#reduce error.good 0 >>= λ _, error.bad 1 >>= λ _, error.bad 2 >>= λ _, error.good 3
/- gives `error.bad 1`, while -/
#reduce error.good 0 >>= λ _, error.bad 2 >>= λ _, error.bad 1 >>= λ _, error.good 3
/- gives `error.bad 2`. -/

/- 2.4 (1 bonus point). Prove the following composition law for `mmap`, which
holds for commutative monads.

Hint: You will need structural induction. -/

lemma mmap_mmap {m : Type → Type} [comm_lawful_monad m]
    {α β γ : Type} (f : α → m β) (g : β → m γ) (as : list α) :
  (mmap f as >>= mmap g) = mmap (λa, f a >>= g) as :=
begin
  induction' as,
  case nil {
    simp [mmap, lawful_monad.pure_bind],
  },
  case cons : a as {
    calc  mmap f (a :: as) >>= mmap g
        = do {
            b ← f a,
            bs ← mmap f as,
            pure (list.cons b bs)
          } >>= mmap g :
      by simp [mmap]
    ... = do {
            b ← f a,
            bs ← mmap f as,
            mmap _ (list.cons b bs)
          } :
      by simp [lawful_monad.pure_bind, lawful_monad.bind_assoc]
    ... = do {
            b ← f a,
            bs ← mmap f as,
            c ← g b,
            cs ← mmap g bs,
            pure (list.cons c cs)
          } :
      by simp [mmap, lawful_monad.bind_assoc]
    ... = do {
            b ← f a,
            c ← g b,
            bs ← mmap f as,
            cs ← mmap g bs,
            pure (c :: cs)
          } :
      by rw comm_lawful_monad.bind_comm
    ... = do {
            c ← (λ a, f a >>= g) a,
            cs ← mmap f as >>= mmap g,
            pure (list.cons c cs)
          } :
      by simp [lawful_monad.bind_assoc]
    ... = do {
            c ← (λ a, f a >>= g) a,
            cs ← mmap (λ a, f a >>= g) as,
            pure (list.cons c cs)
          } :
      by simp [ih]
    ... = mmap (λa, f a >>= g) (a :: as) :
      by simp [mmap],
  },
end

end LoVe
