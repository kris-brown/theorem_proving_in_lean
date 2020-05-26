import data.list.basic

-- Section 5.1: Entering tactic mode
namespace s51
    theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
    begin
    apply and.intro,
    exact hp,
    apply and.intro,
    exact hq,
    exact hp
    end
    #print test

    -- Shorter version, compound exprs
    theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
    begin
    apply and.intro hp,
    exact and.intro hq hp
    end

    -- Concentation of tactics
    theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
    begin
    apply and.intro hp; exact and.intro hq hp
    end

    -- Special keyword for a single-tactic proof
    theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
    by exact and.intro hp (and.intro hq hp)

    -- need to tell Lean which section variables can be in proof
    variables {p q : Prop} (hp : p) (hq : q)
    include hp hq
    example : p ∧ q ∧ p :=
    begin
    apply and.intro hp,
    exact and.intro hq hp
    end

    omit hp hq -- undoing an "include"

    -- Alternative way of getting section variables into a proof
    example : p ∧ q ∧ p :=
    let hp := hp, hq := hq in -- here
    begin
    apply and.intro hp,
    exact and.intro hq hp
    end


end s51

-- Section 5.2: Basic Tactics
namespace s52
    -- intro introduces a hypothesis
    example (α : Type) : α → α :=
    begin
    intro a,
    exact a
    end

    example (α : Type) : ∀ x : α, x = x :=
    begin
    intro x,
    exact eq.refl x
    end

    -- plural intros takes list of names
    example : ∀ a b c : ℕ, a = b → a = c → c = b :=
    begin
    intros a b c h₁ h₂,
    exact eq.trans (eq.symm h₂) h₁
    end

    -- "assumption" looks through context of the current goal and applies something that matches
    variables x y z w : ℕ
    example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
    begin
    apply eq.trans h₁,
    apply eq.trans h₂,
    assumption   -- applied h₃
    end
    -- Will unify variables if necessary
    example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
    begin
    apply eq.trans,
    assumption,     -- solves x = ?m_1 with h₁
    apply eq.trans,
    assumption,     -- solves y = ?m_1 with h₂
    assumption      -- solves z = w with h₃
    end


    --  without any args, intros chooses names + introduces as many vars as it can
    example : ∀ a b c : ℕ, a = b → a = c → c = b :=
    begin
    intros,
    apply eq.trans,
    apply eq.symm,
    assumption,     -- solves y = ?m_1 with h₂
    assumption      -- solves z = w with h₃
    end

    -- refl/symmetry/transitivity  more general than eq.refl/eq.sym/eq.trans
    example (y : ℕ) : (λ x : ℕ, 0) y = 0 :=
    begin
    refl
    end

    example (x : ℕ) : x ≤ x :=
    begin
    refl
    end

    -- Use them to do the above proof again
    example : ∀ a b c : ℕ, a = b → a = c → c = b :=
    begin
    intros,
    transitivity,
    symmetry,
    assumption,
    assumption
    end

    example : ∀ a b c : ℕ, a = b → a = c → c = b :=
    begin
    intros a b c h₁ h₂,
    transitivity a,
    symmetry,
    assumption,
    assumption
    end

    -- Repeat combinator
    example : ∀ a b c : ℕ, a = b → a = c → c = b :=
    begin
    intros,
    apply eq.trans,
    apply eq.symm,
    repeat { assumption } --braces are nested begin...end
    end

    -- apply
    example : ∃ a : ℕ, 5 = a :=
    begin
    apply exists.intro,
    reflexivity
    end

    -- fapply
    example : ∃ a : ℕ, a = a :=
    begin
    fapply exists.intro,
    exact 0,
    reflexivity
    end


end s52

-- Section 5.3: More tactics
namespace s53
    -- Cases, disjunction
    example (p q : Prop) : p ∨ q → q ∨ p :=
    begin
    intro h,
    cases h with hp hq,
    -- case hp : p
    right, exact hp,
    -- case hq : q
    left, exact hq
    end

    -- Cases, conjunction
    example (p q : Prop) : p ∧ q → q ∧ p :=
    begin
    intro h,
    cases h with hp hq,
    constructor, exact hq, exact hp
    end

    -- constructor applies the first constructor of an inductively defined type
    example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
    apply iff.intro,
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
        left, constructor, repeat { assumption },
        right, constructor, repeat { assumption },
    intro h,
        cases h with hpq hpr,
        cases hpq with hp hq,
            constructor, exact hp, left, exact hq,
        cases hpr with hp hr,
            constructor, exact hp, right, exact hr
    end

    -- cases with quantifier
    -- left and right can be used with IDT with exactly two constructors
    example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
    begin
    intro h,
    cases h with x px,
    constructor, left, exact px
    end

    -- Explicit use of existential quantifier
    example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
    begin
    intro h,
    cases h with x px,
    existsi x, left, exact px
    end
    -- semicolon after split means apply the assumption tactic
    -- to both of the goals that are introduced by splitting the conjunction
    example (p q : ℕ → Prop) :
    (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
    begin
    intro h,
    cases h with x hpq,
    cases hpq with hp hq,
    existsi x,
    split; assumption
    end

    -- operating on data, not just props
    universes u v

    def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
    begin
    intro p,
    cases p with ha hb,
    constructor, exact hb, exact ha
    end

    def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
    begin
    intro p,
    cases p with ha hb,
        right, exact ha,
        left, exact hb
    end

    open nat

    example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) :
    P m :=
    begin
    cases m with m', exact h₀, exact h₁ m'
    end

    -- searches for a contradiction among the hypotheses of the current goal
    example (p q : Prop) : p ∧ ¬ p → q :=
    begin
    intro h, cases h, contradiction
    end


end s53

-- Section 5.4: Structuring tactic proofs
namespace s54
    -- Mixing term and tactic style proofs
    example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    begin
    intro h,
    exact
        have hp : p, from h.left,
        have hqr : q ∨ r, from h.right,
        show (p ∧ q) ∨ (p ∧ r),
        begin
        cases hqr with hq hr,
            exact or.inl ⟨hp, hq⟩,
        exact or.inr ⟨hp, hr⟩
        end
    end

    example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
    apply iff.intro,
        intro h,
        cases h.right with hq hr,
        exact or.inl ⟨h.left, hq⟩,
        exact or.inr ⟨h.left, hr⟩,
    intro h,
    cases h with hpq hpr,
        exact ⟨hpq.left, or.inl hpq.right⟩,
    exact ⟨hpr.left, or.inr hpr.right⟩
    end

    --Rewrite above, noting show works in tactic mode and "from" = "exact"
    example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
    apply iff.intro,
        intro h,
        cases h.right with hq hr,
        show (p ∧ q) ∨ (p ∧ r),
            from or.inl ⟨h.left, hq⟩,
        show (p ∧ q) ∨ (p ∧ r),
            from or.inr ⟨h.left, hr⟩,
    intro h,
    cases h with hpq hpr,
        show p ∧ (q ∨ r),
        from ⟨hpq.left, or.inl hpq.right⟩,
        show p ∧ (q ∨ r),
        from ⟨hpr.left, or.inr hpr.right⟩
    end

    -- Or don't use from to remain in tactic mode
    example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
    apply iff.intro,
        intro h,
        cases h.right with hq hr,
        show (p ∧ q) ∨ (p ∧ r),
            { left, split, exact h.left, assumption },
        show (p ∧ q) ∨ (p ∧ r),
            { right, split, exact h.left, assumption },
    intro h,
    cases h with hpq hpr,
        show p ∧ (q ∨ r),
        { cases hpq, split, assumption, left, assumption },
        show p ∧ (q ∨ r),
        { cases hpr, split, assumption, right, assumption }
    end

    -- Show can rewrite something to something definitionally equiv
    example (n : ℕ) : n + 1 = nat.succ n :=
    begin
    show nat.succ n = nat.succ n,
    reflexivity
    end
    -- When there are multiple goals, use show to focus on a particular one to work on
    example (p q : Prop) : p ∧ q → q ∧ p :=
    begin
    intro h,
    cases h with hp hq,
    split,
    show q, from hq,
    show p, from hp
    end

    example (p q : Prop) : p ∧ q → q ∧ p :=
    begin
    intro h,
    cases h with hp hq,
    split,
    show p, from hp,
    show q, from hq
    end

    -- "have" introduces new subgoal, like with terms
    example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
        have hpq : p ∧ q,
        from and.intro hp hq,
        left, exact hpq,
    have hpr : p ∧ r,
        from and.intro hp hr,
    right, exact hpr
    end
    -- Again, but don't use from to remain in tactic mode
    example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
        have hpq : p ∧ q,
        split; assumption,
        left, exact hpq,
    have hpr : p ∧ r,
        split; assumption,
    right, exact hpr
    end

    -- Omit the label of "have" and refer to it with 'this'
    example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
        have : p ∧ q,
        split; assumption,
        left, exact this,
    have : p ∧ r,
        split; assumption,
    right, exact this
    end

    -- using 'have' with ':=' is the same as from
    example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    begin
    intro h,
    have hp : p := h.left,
    have hqr : q ∨ r := h.right,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
        exact or.inl ⟨hp, hq⟩,
    exact or.inr ⟨hp, hr⟩
    end

    -- Let creates abbreviation rather than a new fact (like 'have' does)
    example : ∃ x, x + 2 = 8 :=
    begin
    let a : ℕ := 3 * 2,
    existsi a,
    reflexivity
    end

    -- In a nested block, Lean focuses on the first goal,
    --generates an error if it has not been fully solved at the end of the block.
    example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
    apply iff.intro,
    begin
        intro h,
        cases h.right with hq hr,
        begin
        show (p ∧ q) ∨ (p ∧ r),
            exact or.inl ⟨h.left, hq⟩
        end,
        show (p ∧ q) ∨ (p ∧ r),
        exact or.inr ⟨h.left, hr⟩
    end,
    intro h,
    cases h with hpq hpr,
    begin
        show p ∧ (q ∨ r),
        exact ⟨hpq.left, or.inl hpq.right⟩
    end,
    show p ∧ (q ∨ r),
        exact ⟨hpr.left, or.inr hpr.right⟩
    end

    -- Abbreviate nested begin..end with curly braces
    example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
    apply iff.intro,
    { intro h,
        cases h.right with hq hr,
        { show (p ∧ q) ∨ (p ∧ r),
            exact or.inl ⟨h.left, hq⟩ },
        show (p ∧ q) ∨ (p ∧ r),
        exact or.inr ⟨h.left, hr⟩ },
    intro h,
    cases h with hpq hpr,
    { show p ∧ (q ∨ r),
        exact ⟨hpq.left, or.inl hpq.right⟩ },
    show p ∧ (q ∨ r),
        exact ⟨hpr.left, or.inr hpr.right⟩
    end

    -- Final example
    example (p q : Prop) : p ∧ q ↔ q ∧ p :=
    begin
    apply iff.intro,
    { intro h,
        have hp : p := h.left,
        have hq : q := h.right,
        show q ∧ p,
        exact ⟨hq, hp⟩ },
    intro h,
    have hp : p := h.right,
    have hq : q := h.left,
    show p ∧ q,
        exact ⟨hp, hq⟩
    end

end s54

-- Section 5.5: Tactic combinators
namespace s55
    -- comma applies tactics in sequence
    example (p q : Prop) (hp : p) : p ∨ q :=
    begin left, assumption end
    --semi applies in parallel
    example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
    by split; assumption
    --or else combinator
    example (p q : Prop) (hp : p) : p ∨ q :=
    by { left, assumption } <|> { right, assumption}

    example (p q : Prop) (hq : q) : p ∨ q :=
    by { left, assumption } <|> { right, assumption}

    -- tactics are just terms
    meta def my_tac : tactic unit :=
    `[ repeat { {left, assumption} <|> right <|> assumption } ]

    example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
    by my_tac

    example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
    by my_tac

    example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
    by my_tac

    -- repeat {try t} will loop forever, because the inner tactic never fails

    -- all goals
    example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ q ∧ r :=
    begin
    split,
    all_goals { try {split} },
    all_goals { assumption }
    end
    --any goals
    example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ q ∧ r :=
    begin
    split,
    any_goals { split },
    any_goals { assumption }
    end

    example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
    by repeat { any_goals { split <|> assumption} }

end s55

-- Section 5.6: Rewriting
section s56

    variables (f : ℕ → ℕ) (k : ℕ)
    example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
    begin
    rw h₂, -- replace k with 0
    rw h₁  -- replace f 0 with 0
    end


    example (x y : ℕ) (p : ℕ → Prop) (q : Prop) (h : q → x = y)
    (h' : p y) (hq : q) : p x :=
    by { rw (h hq), assumption }


    example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
    by rw [h₂, h₁]

    variables (a b : ℕ)

    example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 :=
    begin
    rw [←h₁, h₂]
    end

    example (a b c : ℕ) : a + b + c = a + c + b :=
    begin
    rw [add_assoc, add_comm b, ←add_assoc]
    end

    example (a b c : ℕ) : a + b + c = a + c + b :=
    begin
    rw [add_assoc, add_assoc, add_comm b]
    end

    example (a b c : ℕ) : a + b + c = a + c + b :=
    begin
    rw [add_assoc, add_assoc, add_comm _ b]
    end

    -- By default, rw rewrites the goal, but we can make it rewrite hypotheses

    example (h : a + 0 = 0) : f a = f 0 :=
    by { rw add_zero at h, rw h }


    -- Rewriting arbitrary structures
    universe u

    def tuple (α : Type u) (n : ℕ) :=
    { l : list α // list.length l = n }

    variables {α : Type u} {n : ℕ}

    example (h : n = 0) (t : tuple α n) : tuple α 0 :=
    begin
    rw h at t,
    exact t
    end

    example {α : Type u} [ring α] (a b c : α) :
    a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
    begin
    rw [mul_zero, mul_zero, zero_mul, zero_mul],
    repeat { rw add_zero }
    end

    example {α : Type u} [group α] {a b : α} (h : a * b = 1) :
    a⁻¹ = b :=
    by rw [←(mul_one a⁻¹), ←h, inv_mul_cancel_left]


end s56

-- Section 5.7 Simplifier
section s57
section
variables (x y z w : ℕ) (p : ℕ → Prop)
variable  (h : p (x * y))

example : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
by simp

include h
example : p ((x + 0) * (0 + y * 1 + z * 0)) :=
by { simp, assumption }


universe u
variable {α : Type}
open list

example (xs : list ℕ) :
  reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
by simp

example (xs ys : list α) :
  length (reverse (xs ++ ys)) = length xs + length ys :=
by simp

-- As with rw, can simplify a hypothesis

example (h : p ((x + 0) * (0 + y * 1 + z * 0))) :
  p (x * y) :=
by { simp at h, assumption }
-- Wildcard to simplify everything

local attribute [simp] mul_comm mul_assoc mul_left_comm

example (h : p (x * y + z * w  * x)) : p (x * w * z + y * x) :=
by { simp at *, assumption }

example (h₁ : p (1 * x + y)) (h₂ : p  (x * z * 1)) :
  p (y + 0 + x) ∧ p (z * x) :=
by { simp at *, split; assumption }

section
local attribute [simp] mul_comm mul_assoc mul_left_comm

example : x * y + z * w  * x = x * w * z + y * x :=
by simp

example (h : p (x * y + z * w  * x)) : p (x * w * z + y * x) :=
begin simp, simp at h, assumption end
end
end

-- Common strategy
variables (f : ℕ → ℕ) (k : ℕ)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
by simp [h₁, h₂]

-- Again but simpler
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
by simp *
section
variables (p q r : Prop)

example (hp : p) : p ∧ q ↔ q :=
by simp *

example (hp : p) : p ∨ q :=
by simp *

example (hp : p) (hq : q) : p ∧ (q ∨ r) :=
by simp *
end

section
variables (u w x x' y y' z : ℕ) (p : ℕ → Prop)

example (h₁ : x + 0 = x') (h₂ : y + 0 = y') :
  x + y + 0 = x' + y' :=
by { simp at *, simp * }

-- simplify all the hypotheses, and then use them to prove the goal
example (h₁ : x = y + z) (h₂ : w = u + x) (h₃ : p (z + y + u)) :
  p w  :=
by { simp at *, simp * }
end

-- Make new definitions to add to simp's power

open list
universe u
variables {α : Type} (x y z : α) (xs ys zs : list α)

def mk_symm (xs : list α) := xs ++ reverse xs
theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by { unfold mk_symm, simp }
theorem reverse_mk_symm2 (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]
example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp [reverse_mk_symm]

example (xs ys : list ℕ) (p : list ℕ → Prop)
    (h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp [reverse_mk_symm] at h; assumption

-- Declare something to be simp
@[simp] theorem reverse_mk_symm3 (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp

example (xs ys : list ℕ) (p : list ℕ → Prop)
    (h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp at h; assumption

end s57

-- Section 5.
section s5
end s5