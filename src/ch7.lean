import tactic

-- Section 7.1: Enumerated Types
namespace s71

  inductive weekday : Type
  | sunday : weekday
  | monday : weekday
  | tuesday : weekday
  | wednesday : weekday
  | thursday : weekday
  | friday : weekday
  | saturday : weekday
  #check weekday.sunday
  #check weekday.monday

  open weekday

  #check sunday
  #check monday

  -- rec on

  def number_of_day (d : weekday) : ℕ :=
  weekday.rec_on d 1 2 3 4 5 6 7

  #reduce number_of_day weekday.sunday
  #reduce number_of_day weekday.monday
  #reduce number_of_day weekday.tuesday


  -- Less general, cases on
  def number_of_day2 (d : weekday) : ℕ :=
  weekday.cases_on d 1 2 3 4 5 6 7

  -- Group functions associated with datatype
  namespace weekday
    @[reducible]
    private def cases_on := @weekday.cases_on

    def number_of_day (d : weekday) : nat :=
    cases_on d 1 2 3 4 5 6 7
  end weekday

  #reduce weekday.number_of_day weekday.sunday

  open weekday (renaming cases_on → cases_on)

  #reduce number_of_day sunday
  #check cases_on

  namespace weekday
    def next (d : weekday) : weekday :=
    weekday.cases_on d monday tuesday wednesday thursday friday
      saturday sunday

    def previous (d : weekday) : weekday :=
    weekday.cases_on d saturday sunday monday tuesday wednesday
      thursday friday

    #reduce next (next tuesday)
    #reduce next (previous tuesday)

    example : next (previous tuesday) = tuesday := rfl
  end weekday


  -- Prove an invariant
  open weekday (renaming cases_on → cases_on)

    theorem next_previous (d: weekday) :
      next (previous d) = d :=
    weekday.cases_on d
      (show next (previous sunday) = sunday, from rfl)
      (show next (previous monday) = monday, from rfl)
      (show next (previous tuesday) = tuesday, from rfl)
      (show next (previous wednesday) = wednesday, from rfl)
      (show next (previous thursday) = thursday, from rfl)
      (show next (previous friday) = friday, from rfl)
      (show next (previous saturday) = saturday, from rfl)

  --more succinct
    theorem next_previous2 (d: weekday) :
      next (previous d) = d :=
    weekday.cases_on d rfl rfl rfl rfl rfl rfl rfl

  -- Use parallel combinator ; in tactic proof
  theorem next_previous3 (d: weekday) :
      next (previous d) = d :=
    by apply weekday.cases_on d; refl

  -- standard library enum types
  namespace hidden
  inductive empty : Type

  inductive unit : Type
  | star : unit

  inductive bool : Type
  | ff : bool
  | tt : bool
  end hidden

end s71

-- Section 7.2: Constructors with Arguments
namespace s72
  universes u v

  inductive prodd (α : Type u) (β : Type v)
  | mk : α → β → prodd

  inductive summ (α : Type u) (β : Type v)
  | inl {} : α → summ
  | inr {} : β → summ

  def fst {α : Type u} {β : Type v} (p : prodd α β) : α :=
  prodd.rec_on p (λ a b, a)

  def snd {α : Type u} {β : Type v} (p : α × β) : β :=
  prod.rec_on p (λ a b, b)

  def prod_example (p : bool × ℕ) : ℕ :=
  prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))

  #reduce prod_example (tt, 3)
  #reduce prod_example (ff, 3)


  def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
  sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1)

  #reduce sum_example (sum.inl 3)
  #reduce sum_example (sum.inr 3)

  -- simultaneously introduces the inductive type, prod, its constructor, mk, the usual eliminators (rec and rec_on), as well as the projections, fst and snd, as defined above.
  structure prod3 (α β : Type) :=
  mk :: (fst : α) (snd : β)


  structure color := (red : nat) (green : nat) (blue : nat)
  def yellow := color.mk 255 255 0
  #reduce color.red yellow


  structure Semigroup :=
  (carrier : Type u)
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))



  inductive sigma {α : Type u} (β : α → Type v)
  | dpair : Π a : α, β a → sigma

  inductive option (α : Type u)
  | none {} : option
  | some    : α → option

  inductive inhabited (α : Type u)
  | mk : α → inhabited

end s72

-- Section 7.3: Inductively defined propositions
namespace s73
  inductive false : Prop

  inductive true : Prop
  | intro : true

  inductive and (a b : Prop) : Prop
  | intro : a → b → and

  inductive or (a b : Prop) : Prop
  | intro_left  : a → or
  | intro_right : b → or

  universe u
  inductive Exists {α : Type u} (p : α → Prop) : Prop
  | intro : ∀ (a : α), p a → Exists

  def exists.intro := @Exists.intro


  -- false, true, and, + or are perfectly analogous to the definitions of empty, unit, prod, and sum.
  --difference is that the first group yields elements of Prop, and the second yields elements of Type u

  --  sort of a hybrid between ∃ x : α, P and Σ x : α, P.

  inductive subtype {α : Type u} (p : α → Prop)
  | mk : Π x : α, p x → subtype


  section
  structure subtype2 {α : Sort u} (p : α → Prop) :=
  (val : α) (property : p val)
  variables {α : Type u} (p : α → Prop)

  #check subtype2 p
  #check { x : α // p x}
  end

end s73

-- Section 7.4: Defining the nats
namespace s74
  inductive nat : Type
  | zero : nat
  | succ : nat → nat
  #check @nat.rec_on -- 'motive C', major premise n, and two minor premises

  namespace nat
    def add (m n : nat) : nat :=
    nat.rec_on n m (λ _ add_m_n, succ add_m_n)

    -- try it out
    #reduce add (succ zero) (succ (succ zero))


    instance : has_zero nat := has_zero.mk zero
    instance : has_add nat := has_add.mk add

    theorem add_zero (m : nat) : m + 0 = m := rfl
    theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl


    theorem zero_add (n : nat) : 0 + n = n :=
    nat.rec_on n
      (show 0 + zero = zero, from rfl)
      (assume n,
        assume ih : 0 + n = n,
        show 0 + succ n = succ n, from
          calc
            0 + succ n = succ (0 + n) : rfl
              ... = succ n : by rw ih)


    theorem zero_add' (n : nat) : 0 + n = n :=
    nat.rec_on n rfl (λ n ih, by rw [add_succ, ih])

    theorem zero_add''(n : nat) : 0 + n = n :=
    nat.rec_on n rfl (λ n ih, by simp only [add_succ, ih])


    theorem add_assoc (m n k : nat) : m + n + k = m + (n + k) :=
    nat.rec_on k
      (show m + n + 0 = m + (n + 0), from rfl)
      (assume k,
        assume ih : m + n + k = m + (n + k),
        show m + n + succ k = m + (n + succ k), from
          calc
            m + n + succ k = succ (m + n + k) : rfl
              ... = succ (m + (n + k)) : by rw ih
              ... = m + succ (n + k) : rfl
              ... = m + (n + succ k) : rfl)

    theorem add_assoc' (m n k : nat) : m + n + k = m + (n + k) :=
    nat.rec_on k rfl (λ k ih, by simp only [add_succ, ih])


    theorem succ_add (m n : nat) : succ m + n = succ (m + n) :=
    nat.rec_on n
      (show succ m + 0 = succ (m + 0), from rfl)
      (assume n,
        assume ih : succ m + n = succ (m + n),
        show succ m + succ n = succ (m + succ n), from
          calc
            succ m + succ n = succ (succ m + n) : rfl
              ... = succ (succ (m + n)) : by rw ih
              ... = succ (m + succ n) : rfl)


    theorem succ_add' (m n : nat) : succ m + n = succ (m + n) :=
    nat.rec_on n rfl (λ n ih, by simp only [add_succ, ih])


  theorem add_comm (m n : nat) : m + n = n + m :=
  nat.rec_on n
    (show m + 0 = 0 + m, by rw [nat.zero_add, nat.add_zero])
    (assume n,
      assume ih : m + n = n + m,
      calc
        m + succ n = succ (m + n) : rfl
          ... = succ (n + m) : by rw ih
          ... = succ n + m : by rw succ_add)

  end nat

end s74

-- Section 7.5: Other recursive datatypes
namespace s75
  universe u
  inductive list (α : Type u)
  | nil {} : list
  | cons : α → list → list

  namespace list

    variable {α : Type}

    notation h :: t  := cons h t

    def append (s t : list α) : list α :=
    list.rec t (λ x l u, x::u) s

    notation s ++ t := append s t

    theorem nil_append (t : list α) : nil ++ t = t := rfl

    theorem cons_append (x : α) (s t : list α) :
      x::s ++ t = x::(s ++ t) := rfl

    notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

    section
      open nat
      #check [1, 2, 3, 4, 5]
      #check ([1, 2, 3, 4, 5] : list int)
    end


  end list

  inductive binary_tree
  | leaf : binary_tree
  | node : binary_tree → binary_tree → binary_tree

  inductive cbtree
  | leaf : cbtree
  | sup : (ℕ → cbtree) → cbtree

  namespace cbtree

  def succ (t : cbtree) : cbtree :=
  sup (λ n, t)

  def omega : cbtree :=
  sup (λ n, nat.rec_on n leaf (λ n t, succ t))

  end cbtree

end s75

-- Section 7.6: Tactics for inductive types
namespace s76
  open nat
  variable p : ℕ → Prop

  example (hz : p 0) (hs : ∀ n, p (succ n)) : ∀ n, p n :=
  begin
    intro n,
    cases n,
    { exact hz },  -- goal is p 0
    apply hs       -- goal is a : ℕ ⊢ p (succ a)
  end


  example (n : ℕ) (h : n ≠ 0) : succ (pred n) = n :=
  begin
    cases n with m,
    -- first goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
      { apply (absurd rfl h) },
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ a)) = succ a
    reflexivity
  end

  def f37 (n : ℕ) : ℕ :=
  begin
    cases n, exact 3, exact 7
  end

  example : f37 0 = 3 := rfl
  example : f37 5 = 7 := rfl
  universe u

  def tuple (α : Type u) (n : ℕ) :=
    { l : list α // list.length l = n }

  variables {α : Type u} {n : ℕ}

  def f {n : ℕ} (t : tuple α n) : ℕ :=
  begin
    cases n, exact 3, exact 7
  end
  def myList : list ℕ := 0 :: 1 :: 2 :: list.nil
  def my_tuple : tuple ℕ 3 :=  ⟨myList, rfl⟩
  def my_tuple2 : tuple ℕ 0 :=  ⟨list.nil, rfl⟩

  example : f my_tuple = 7 := rfl
  example : f my_tuple2 = 3 := rfl

  inductive foo : Type
  | bar1 : ℕ → ℕ → foo
  | bar2 : ℕ → ℕ → ℕ → foo

  def silly (x : foo) : ℕ :=
  begin
    cases x with a b c d e,
    exact b,    -- a, b    are in the context
    exact e     -- c, d, e are in the context
  end

  --Difficult to keep track of which variables are associated w/ which case
  -- Same as above but better syntax
  def silly' (x : foo) : ℕ :=
  begin
    cases x,
      case foo.bar2 : c d e -- Can do in any order
        { exact e },
      case foo.bar1 : a b
        { exact b }
  end


  --Cases on an arbitrary expr
  open nat
  variable natprop : ℕ → Prop

  example (hz : natprop 0) (hs : ∀ n, natprop (succ n)) (m k : ℕ) :
    natprop (m + 3 * k) :=
  begin
    cases (m + 3 * k),
    { exact hz },  -- goal is natprop 0
    apply hs       -- goal is a : ℕ ⊢ natprop (succ a)
  end

  -- above is equivalent to this

  example (hz : natprop 0) (hs : ∀ n, natprop (succ n)) (m k : ℕ) :
    natprop (m + 3 * k) :=
  begin
    generalize : (m + 3 * k) = n,
    cases n,
    { exact hz },  -- goal is natprop 0
    apply hs       -- goal is a : ℕ ⊢ natprop (succ a)
  end


  example (p : Prop) (m n : ℕ)
    (h₁ : m < n → p) (h₂ : m ≥ n → p) : p :=
  begin
    cases lt_or_ge m n with hlt hge,
    { exact h₁ hlt },
    exact h₂ hge
  end


  #check nat.sub_self

  example (m n : ℕ) : m - n = 0 ∨ m ≠ n :=
  begin
    cases decidable.em (m = n) with heq hne,
    { rw heq,
      left, exact nat.sub_self n },
    right, exact hne
  end

  def f' (m k : ℕ) : ℕ :=
  begin
    cases m - k, exact 3, exact 7
  end

  example : f' 5 7 = 3 := rfl
  example : f' 10 2 = 7 := rfl

  -- Induction instead of 'cases'
  theorem zero_add (n : ℕ) : 0 + n = n :=
  begin
    induction n with n ih,
      refl,
    rw [add_succ, ih]
  end

  theorem zero_add' (n : ℕ) : 0 + n = n :=
  begin
    induction n,
    case zero : { refl },
    case succ : n ih { rw [add_succ, ih]}
  end

  theorem succ_add (m n : ℕ) : succ m + n = succ (m + n) :=
  begin
    induction n,
    case zero : { refl },
    case succ : n ih { rw [add_succ, ih] }
  end

  theorem add_comm (m n : ℕ) : m + n = n + m :=
  begin
    induction n,
    case zero : { rw zero_add, refl },
    case succ : n ih { rw [add_succ, ih, succ_add] }
  end

  theorem zero_add'' (n : ℕ) : 0 + n = n :=
  by induction n; simp only [*, add_zero, add_succ]

  theorem succ_add' (m n : ℕ) : succ m + n = succ (m + n) :=
  by induction n; simp only [*, add_zero, add_succ]

  theorem add_comm' (m n : ℕ) : m + n = n + m :=
  by induction n;
      simp only [*, add_zero, add_succ, succ_add, zero_add]

  theorem add_assoc (m n k : ℕ) : m + n + k = m + (n + k) :=
  by induction k; simp only [*, add_zero, add_succ]

  -- Injectivity of the IDT constructors
  example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
    n + k = m + k :=
  begin
    injection h   with h',
    injection h' with h'',
    rw h''
  end

  example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
    n + k = m + k :=
  begin
    injections with h' h'',
    rw h''
  end

  example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
    n + k = m + k :=
  by injections; simp *

  example (m n : ℕ) (h : succ m = 0) : n = n + 7 :=
  by injections

  example (m n : ℕ) (h : succ m = 0) : n = n + 7 :=
  by contradiction

  example (h : 7 = 4) : false :=
  by injections


end s76

-- Section 7.7: inductive families
namespace s77

  universe u
  open nat
  inductive vector (α : Type u) : nat → Type u
  | nil {}                              : vector zero
  | cons {n : ℕ} (a : α) (v : vector n) : vector (succ n)


  inductive eq {α : Sort u} (a : α) : α → Prop
  | refl : eq a

  @[elab_as_eliminator]
  theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : eq a b) (h₂ : p a) : p b :=
  eq.rec h₂ h₁

  #check subst

  theorem symm {α : Type u} {a b : α} (h : eq a b) : eq b a :=
  subst h (eq.refl a)


end s77

-- Section 7.9: mutual and nested inductive types
namespace s79
  mutual inductive even, odd
  with even : ℕ → Prop
  | even_zero : even 0
  | even_succ : ∀ n, odd n → even (n + 1)
  with odd : ℕ → Prop
  | odd_succ : ∀ n, even n → odd (n + 1)


  universe u

  mutual inductive tree, list_tree (α : Type u)
  with tree : Type u
  | node : α → list_tree → tree
  with list_tree : Type u
  | nil {} : list_tree
  | cons    : tree → list_tree → list_tree

  -- this is much more convenient, does the same thing under the hood (allowing us to use list theorems)
  inductive tree' (α : Type u)
  | mk : α → list tree' → tree'



end s79

-- Exercises
namespace s7x

-- 1
--define multiplication, the predecessor function, truncated subtraction, and exponentiation
  namespace nat
    def mult (m n : ℕ) : ℕ :=
    nat.rec_on n 0 (λ _ add_m_n, m + add_m_n)
    #reduce mult 6 4

    def pred (n : nat) : nat :=
    nat.rec_on n 0 (λ n pred_n, n)
    #reduce pred 21

    def tsub (m n : nat) : nat :=
    nat.rec_on n m (λ n tsub_m_n, pred tsub_m_n)
    #reduce tsub 21 4

    def exp (m n : nat) : nat :=
    nat.rec_on n 1 (λ n exp_m_n, mult m exp_m_n)
    #reduce exp 3 4


  end nat

--2a


variable {α : Type}
open list

--lemma append_nil (t : list α) : t ++ nil = t := list.append_nil

example  (s t : list α) : length (s ++ t) = length s + length t :=
  list.rec_on t
    (show length (s ++ nil) = length s + length nil, by
    calc
      length (s ++ nil) = length s : by rw append_nil
        ... = length s + length nil : by refl)
    (assume x : α,
    assume y : list α ,
    assume ih : length (s ++ y) = length (s) + length(y),
    show length (s ++ x::y) = length (s) + length(x::y), by
    calc
      length (s ++ x::y) = length (s ++ y) + 1 : by simp
      ... = length (s) + length(x::y): by simp )

example (t : list α) : list.length (list.reverse t) = list.length t := sorry

example (t : list α) : list.reverse (list.reverse t) = t := sorry


-- 2b implement the following
theorem append_nil (t : list α) : t ++ list.nil = t :=
  list.rec_on t
  (show nil ++ nil = nil, by refl)
  (assume x : α,
   assume y : list α,
   assume ih : y ++ nil = y,
   show x::y ++ nil = x::y , by {injections; simp})

theorem append_assoc (r s t : list α) :
r ++ s ++ t = r ++ (s ++ t) := sorry


--3
--4

--5


theorem trans {α : Type u} {a b c : α}
  (h₁ : eq a b) (h₂ : eq b c) : eq a c :=
sorry

theorem congr {α β : Type u} {a b : α} (f : α → β)
  (h : eq a b) : eq (f a) (f b) :=
sorry

end s7x
