#check function.const
-- Section 4.1: The universal quantifier
namespace s41
    section
        variables (α : Type) (p q : α → Prop)
        -- ∀ is more natural than Π when p is a proposition
        example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
        assume h : ∀ x : α, p x ∧ q x,
        assume y : α, -- prove for an arbitrary α
        show p y, from (h y).left


        -- Alpha-equivalent version
        example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
        assume h : ∀ x : α, p x ∧ q x,
        assume z : α,
        show p z, from and.elim_left (h z)
    end
    -- Transitivity
    section
        variables (α : Type)  (r : α → α → Prop)
        variable  trans_r : ∀ x y z, r x y → r y z → r x z

        variables a b c : α
        variables (hab : r a b) (hbc : r b c)

        #check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
        #check trans_r a b c
        #check trans_r a b c hab
        #check trans_r a b c hab hbc
    end
    -- Less tedious with implicit variables
    section
        universe u
        variables (β : Type u) (r : β  → β  → Prop)
        variable  trans_r : ∀ {x y z}, r x y → r y z → r x z

        variables (a b c : β)
        variables (hab : r a b) (hbc : r b c)

        #check trans_r
        #check trans_r hab
        #check trans_r hab hbc
    end

    -- Equivalence relation
    variables (α : Type) (r : α → α → Prop)
    --variables (r : α → α → Prop)

    variable refl_r : ∀ x, r x x
    variable symm_r : ∀ {x y}, r x y → r y x
    variable trans_r : ∀ {x y z}, r x y → r y z → r x z

    example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) :
    r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd

end s41
-- Section 4.2: Equality
namespace s42
    #check eq.refl    -- ∀ (a : ?M_1), a = a
    #check eq.symm    -- ?M_2 = ?M_3 → ?M_3 = ?M_2
    #check eq.trans   -- ?M_2 = ?M_3 → ?M_3 = ?M_4 → ?M_2 = ?M_4

    section
        universe u

        #check @eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
        #check @eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
        #check @eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α},
                            --   a = b → b = c → a = c

        variables (α : Type u) (a b c d : α)
        variables (hab : a = b) (hcb : c = b) (hcd : c = d)

        example : a = d :=
        eq.trans (eq.trans hab (eq.symm hcb)) hcd
        -- Equivalent, using the 'projection' notation
        example : a = d := (hab.trans hcb.symm).trans hcd
    end

    section
        -- Reflexivity example
        universe u
        variables (α β : Type u)

        example (f : α → β) (a : α) : (λ x, f x) a = f a := eq.refl _
        example (a : α) (b : α) : (a, b).1 = a := eq.refl _
        example : 2 + 3 = 5 := eq.refl _
        -- Shorthand for eq.refl _
        example (f : α → β) (a : α) : (λ x, f x) a = f a := rfl
        example (a : α) (b : α) : (a, b).1 = a := rfl
        example : 2 + 3 = 5 := rfl
    end
    section
    -- = is special equivalenc relation: every assertion respects the equivalence
    universe u

    example (α : Type u) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
    eq.subst h1 h2
    -- shorthand for eq.subst
    example (α : Type u) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
    h1 ▸ h2
    end
    section
        -- More explicit subsitutions: arg, fun, or both arg and fun
        variable α : Type
        variables a b : α
        variables f g : α → ℕ
        variable h₁ : a = b
        variable h₂ : f = g

        example : f a = f b := congr_arg f h₁
        example : f a = g a := congr_fun h₂ a
        example : f a = g b := congr h₂ h₁
        #check congr_arg
    end

    -- Common identities in library
    section
        variables a b c d : ℤ

        example : a + 0 = a := add_zero a
        example : 0 + a = a := zero_add a
        example : a * 1 = a := mul_one a
        example : 1 * a = a := one_mul a
        example : -a + a = 0 := neg_add_self a
        example : a + -a = 0 := add_neg_self a
        example : a - a = 0 := sub_self a
        example : a + b = b + a := add_comm a b
        example : a + b + c = a + (b + c) := add_assoc a b c
        example : a * b = b * a := mul_comm a b
        example : a * b * c = a * (b * c) := mul_assoc a b c
        example : a * (b + c) = a * b + a * c := mul_add a b c
        example : a * (b + c) = a * b + a * c := left_distrib a b c
        example : (a + b) * c = a * c + b * c := add_mul a b c
        example : (a + b) * c = a * c + b * c := right_distrib a b c
        example : a * (b - c) = a * b - a * c := mul_sub a b c
        example : (a - b) * c = a * c - b * c := sub_mul a b c
    end

    section
        variables x y z : ℤ

        example (x y z : ℕ) : x * (y + z) = x * y + x * z := mul_add x y z
        example (x y z : ℕ) : (x + y) * z = x * z + y * z := add_mul x y z
        example (x y z : ℕ) : x + y + z = x + (y + z) := add_assoc x y z

        example (x y : ℕ) :
        (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
        have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
        from mul_add (x + y) x y,
        have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
        from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
        h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm
    end

end s42

-- Section 4.3: Calculational proofs
namespace s43
    section
        variables (a b c d e : ℕ)
        variable h1 : a = b
        variable h2 : b = c + 1
        variable h3 : c = d
        variable h4 : e = 1 + d

        theorem T : a = e :=
        calc
        a     = b      : h1
            ... = c + 1  : h2
            ... = d + 1  : congr_arg _ h3
            ... = 1 + d  : add_comm d (1 : ℕ)
            ... =  e     : eq.symm h4

        -- Multiple rewrites sequentially
        include h1 h2 h3 h4
        theorem T2 : a = e :=
        calc
        a     = d + 1  : by rw [h1, h2, h3]
            ... = 1 + d  : by rw add_comm
            ... =  e     : by rw h4

        -- Apply any rewrite in any order
        theorem T3 : a = e :=
        by simp [h1, h2, h3, h4]



    end
    section
        -- Can use other transitive relations with the calc block
        theorem T4 (a b c d : ℕ)
        (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
        calc
        a     = b     : h1
            ... < b + 1 : nat.lt_succ_self b
            ... ≤ c + 1 : nat.succ_le_succ h2
            ... < d     : h3

        -- Rewriting of the proof in 4.2 in a much more legible way
        example (x y : ℕ) :
        (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
        calc
        (x + y) * (x + y) = (x + y) * x + (x + y) * y  : by rw mul_add
            ... = x * x + y * x + (x + y) * y            : by rw add_mul
            ... = x * x + y * x + (x * y + y * y)        : by rw add_mul
            ... = x * x + y * x + x * y + y * y          : by rw ←add_assoc

        -- Sequential
        example (x y : ℕ) :
        (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
        by rw [mul_add, add_mul, add_mul, ←add_assoc]
        -- Auto simplification
        example (x y : ℕ) :
        (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
        by simp [mul_add, add_mul]

    end

end s43

-- Section 4.4: Existential quantifier
namespace s44
    section
            -- Introduction
            open nat

            example : ∃ x : ℕ, x > 0 :=
            have h : 1 > 0, from zero_lt_succ 0,
            exists.intro 1 h

            example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
            exists.intro 0 h

            example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
            ∃ w, x < w ∧ w < z :=
            exists.intro y (and.intro hxy hyz)

            #check @exists.intro

            -- Anonymous constructor for exists.intro
            example : ∃ x : ℕ, x > 0 :=
            ⟨1, zero_lt_succ 0⟩

            example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
            ⟨0, h⟩

            example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
            ∃ w, x < w ∧ w < z :=
            ⟨y, hxy, hyz⟩

            -- Implicit arguments to exists.intro
            variable g : ℕ → ℕ → ℕ
            variable hg : g 0 0 = 0

            theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
            theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
            theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
            theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

            set_option pp.implicit true  -- display implicit arguments
            #print gex1
            #print gex2
            #print gex3
            #print gex4

    end
    section
        -- Exists elim
        variables (α : Type) (p q : α → Prop)

        example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        exists.elim h -- think as a generalization of or.elim, for each possible x
        (assume w,
            assume hw : p w ∧ q w,
            show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

        -- More convenient way to eliminate ∃

        example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        match h with ⟨w, hw⟩ :=
        ⟨w, hw.right, hw.left⟩
        end

        -- match  “destructs” the ∃  into  components which are used in the body to prove the proposition

        -- Now with type annotation

        example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        match h with ⟨w, hpw, hqw⟩ :=
        ⟨w, hqw, hpw⟩
        end
        -- Even more convenient
        example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

        --Implicit "match" in the assume statement
        example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
        assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

    end
    section
        -- Sum of two even numbers is even
        def is_even (a : nat) := ∃ b, a = 2 * b

        theorem even_plus_even {a b : nat}
        (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
        exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
        exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
        exists.intro (w1 + w2)
            (calc
            a + b = 2 * w1 + 2 * w2  : by rw [hw1, hw2]
                ... = 2*(w1 + w2)      : by rw mul_add)))
        --Succinct
        theorem even_plus_even2 {a b : nat}
        (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
        match h1, h2 with
        ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
        end

    end
    section
        -- A proof that requires classical logic
        -- Knowing that something is false isn't constructively the same
        -- as knowing the thing that makes it false
        open classical

        variables (α : Type) (p : α → Prop)

        example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
        by_contradiction
        (assume h1 : ¬ ∃ x, p x,
            have h2 : ∀ x, ¬ p x, from
            assume x,
            assume h3 : p x,
            have h4 : ∃ x, p x, from  ⟨x, h3⟩,
            show false, from h1 h4,
            show false, from h h2)

    end
end s44

-- Section 4.5: More on proof language
namespace s45

    -- "this" to refer to previous
    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 0 ≤ f 2, from le_trans this (h 1),
    show f 0 ≤ f 3, from le_trans this (h 2)

    -- assumption

    example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 0 ≤ f 2, from le_trans (by assumption) (h 1),
    show f 0 ≤ f 3, from le_trans (by assumption) (h 2)

    -- notation `‹` p `›` := show p, by assumption
    example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    assume : f 0 ≥ f 1,
    assume : f 1 ≥ f 2,
    have f 0 ≥ f 2, from le_trans this ‹f 0 ≥ f 1›,
    have f 0 ≤ f 2, from le_trans (h 0) (h 1),
    show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›

    example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 1 ≤ f 2, from h 1,
    have f 2 ≤ f 3, from h 2,
    show f 0 ≤ f 3, from le_trans ‹f 0 ≤ f 1›
                        (le_trans ‹f 1 ≤ f 2› ‹f 2 ≤ f 3›)

    -- assume hypothesis w/o a label
    example : f 0 ≥ f 1 → f 0 = f 1 :=
    assume : f 0 ≥ f 1,
    show f 0 = f 1, from le_antisymm (h 0) this

    -- anonymous Assumption used later in a proof
    example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    assume : f 0 ≥ f 1,
    assume : f 1 ≥ f 2,
    have f 0 ≥ f 2, from le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›,
    have f 0 ≤ f 2, from le_trans (h 0) (h 1),
    show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›

end s45

-- Exercises
namespace s4x
--1
section
    variables (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := iff.intro
    (assume h :  (∀ x, p x ∧ q x),
        have hp : ∀ x, p x, from (λ a, (h a).left),
        have hq : ∀ x, q x, from (λ a, (h a).right),
        show (∀ x, p x) ∧ (∀ x, q x), from and.intro hp hq)
    (assume h :  (∀ x, p x) ∧ (∀ x, q x),
        (assume a : α,
        show p a ∧ q a, from and.intro (h.left a) (h.right a)))


    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
        assume h : ∀ x, p x → q x,
        assume hp : ∀ x, p x,
        assume a : α,
        have pa : p a, from hp a,
        show q a, from (h a) pa


    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
        assume h : (∀ x, p x) ∨ (∀ x, q x),
        assume a : α,
        show p a ∨ q a, from or.elim h
            (assume hp : ∀ x, p x, or.inl (hp a))
            (assume hq : ∀ x, q x, or.inr (hq a))

    -- Why the reverse implication is not derivable in the last example?
    -- Because some elements may be p whereas other elements may be q.
end

--2
section
    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) :=
        assume a : α, iff.intro
            (assume h : ∀ x : α, r, h a)
            (assume hr : r, λ _, hr)


    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := iff.intro
        (assume h : ∀ x, r → p x,
            assume hr : r,
                assume a : α, h a hr)
        (assume h : r → ∀ x, p x,
            assume a : α,
                assume hr : r, h hr a)


    open classical -- One direction needs it
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := iff.intro
        (assume h : ∀ x, p x ∨ r,
            have emr : r ∨ ¬ r, from em r,
            or.elim emr
                or.inr
                (assume hnr : ¬ r,
                    have hpx: ∀ x, p x, from
                        assume a : α,
                        have hpar : p a ∨ r, from h a,
                        show p a, from or.elim hpar id (flip absurd hnr),
                    or.inl hpx))
        (assume h : (∀ x, p x) ∨ r,
            assume a : α , or.elim h
                (assume hx : ∀ x, p x, or.inl (hx a))
                or.inr)

end

--3: barber paradox
section
    variables (men : Type) (barber : men)
    variable  (shaves : men → men → Prop)

    open classical
    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
    false :=
        have hf: shaves barber barber → ¬shaves barber barber, from (h barber).mp,
        have hfr: ¬shaves barber barber → shaves barber barber, from (h barber).mpr,
        have e : shaves barber barber ∨ ¬ shaves barber barber, from em (shaves barber barber),
        or.elim e
        (assume h: shaves barber barber, absurd h (hf h))
        (assume h : ¬ shaves barber barber, absurd (hfr h) h)
end

--4

namespace hidden

    def divides (m n : ℕ) : Prop := ∃ k, m * k = n

    instance : has_dvd nat := ⟨divides⟩

    def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

    section
    variables m n : ℕ

    #check m ∣ n
    #check m^n
    #check even (m^n +3)
    end

    def prime (n : ℕ) : Prop := ∀ m : ℕ, divides m n → m=1 ∨ m=n

    def infinitely_many_primes : Prop := ∀ n : ℕ, ∃ p: ℕ, prime(p) ∧ p > n

    def Fermat_prime (n : ℕ) : Prop := prime(n) ∧ (∃ m : ℕ, n=2^(2^m))

    def infinitely_many_Fermat_primes : Prop := ∀ n : ℕ, ∃ p: ℕ, Fermat_prime(p) ∧ p > n

    def goldbach_conjecture : Prop :=
        ∀ n : ℕ,
            even(n) ∧ n > 2
                → ∃ a b : ℕ,
                    prime(a) ∧ prime(b) ∧ n=a+b

    def Goldbach's_weak_conjecture : Prop :=
        ∀ n : ℕ,
            ¬ even(n) ∧ n > 5
                → ∃ a b c : ℕ,
                    prime(a) ∧ prime(b) ∧ prime(c) ∧ n=a+b+c


    def Fermat's_last_theorem : Prop :=
        ∀ n : ℕ,
            n > 2
                → ∀ a b c : ℕ,
                    ¬ (a^n+b^n = c^n)

end hidden

--5
section
    open classical

    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    example : (∃ x : α, r) → r :=
        assume h : ∃ x : α, r,
        exists.elim h
        (assume _, id)

    example : r → (∃ x : α, r) :=
        assume hr : r,
        ⟨a, hr⟩

    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro
    (assume h: ∃ x, p x ∧ r,
        match h with ⟨w, pw_r⟩ :=
            and.intro ⟨w, pw_r.left⟩ pw_r.right
        end)
    (assume h: (∃ x, p x) ∧ r,
        match h.left with ⟨w, pw⟩ :=
            ⟨w, and.intro pw h.right⟩
        end)

    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := iff.intro
        (assume h : (∃ x, p x ∨ q x),
            match h with ⟨w, pwqw⟩ :=
                or.elim pwqw
                (assume hl : p w, or.inl ⟨w, hl⟩)
                (assume hr : q w, or.inr ⟨w, hr⟩)
            end )
        (assume h : (∃ x, p x) ∨ (∃ x, q x), or.elim h
            (assume hl: ∃ x, p x,
                match hl with ⟨w,pw⟩ := ⟨w,or.inl pw⟩ end)
            (assume hr: ∃ x, q x,
                match hr with ⟨w,qw⟩ := ⟨w,or.inr qw⟩ end))


    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := iff.intro
        (assume h : ∀ x, p x,
            assume hn : ∃ x, ¬ p x,
            match hn with ⟨w, npw⟩ := absurd (h w) npw end)
        (assume h : ¬ (∃ x, ¬ p x),
            assume z: α,
            have ep: p z ∨ ¬(p z), from em (p z),
            or.elim ep id
                (assume hnpz : ¬(p z), false.elim (h ⟨z, hnpz⟩)))

    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := iff.intro
        (assume h : ∃ x, p x,
            match h with ⟨w, pw⟩ :=
                assume h2: ∀ x, ¬ p x,
                absurd pw (h2 w)
            end)
        (assume h : ¬ (∀ x, ¬ p x),
            have hem: (∃ x, p x) ∨ (¬ ∃ x, p x), from em ∃ x, p x,
            or.elim hem id
                (assume hn: ¬ ∃ x, p x,
                    false.elim (h
                        (assume b: α,
                            have hem2: p b ∨ ¬p b, from em (p b),
                            or.elim hem2
                            (assume hpb: p b, false.elim (hn ⟨b, hpb⟩))
                            id))))

    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := iff.intro
        (assume h : ¬ ∃ x, p x,
            assume b: α,
            have hem: p b ∨ ¬p b, from em (p b),
            or.elim hem
                (assume hpb: p b, false.elim (h ⟨b, hpb⟩))
                id)
        (assume h : ∀ x, ¬ p x,
            assume hx: ∃ x, p x,
            match hx with ⟨w, hpw⟩ :=  absurd hpw (h w) end)

    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := iff.intro
        (assume h : ¬ ∀ x, p x,
            have ep: (∃ x, ¬ p x) ∨ ¬(∃ x, ¬ p x), from em (∃ x, ¬ p x),
            or.elim ep id
                (assume hn :¬(∃ x, ¬ p x),
                    false.elim (h
                        (assume b: α,
                            have hem2: p b ∨ ¬p b, from em (p b),
                            or.elim hem2 id
                                (assume hnpb: ¬ p b, false.elim (hn ⟨b, hnpb⟩))))))
        (assume h : ∃ x, ¬ p x,
            match h with ⟨w, npw⟩ :=
                assume h2: ∀ x, p x,
                    have h3: p w, from h2 w,
                    show false, from absurd h3 npw
            end)


    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := iff.intro
        (assume h : ∀ x, p x → r,
            assume hx : ∃ x, p x,
                match hx with ⟨w, hpw⟩ :=
                    show r, from h w hpw
                end)
        (assume h :  (∃ x, p x) → r,
            assume b: α,
                assume hpb : p b,
                show r, from h ⟨b, hpb⟩)


    example : (∃ x, p x → r) ↔ (∀ x, p x) → r := iff.intro
        (assume h : (∃ x, p x → r),
            (assume hb: ∀ x, p x,
                match h with ⟨w, hpwr⟩ :=
                    show r, from hpwr (hb w)
                end))
        (assume h1 : (∀ x, p x) → r,
            show ∃ x, p x → r, from
            by_cases
                (assume hap : ∀ x, p x, ⟨a, λ h', h1 hap⟩)
                (assume hnap : ¬ ∀ x, p x,
                by_contradiction
                    (assume hnex : ¬ ∃ x, p x → r,
                    have hap : ∀ x, p x, from
                        assume x,
                        by_contradiction
                        (assume hnp : ¬ p x,
                            have hex : ∃ x, p x → r,
                            from ⟨x, (assume hp, absurd hp hnp)⟩,
                            show false, from hnex hex),
                    show false, from hnap hap)))



    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := iff.intro
        (assume h : (∃ x, r → p x),
            (assume hr : r,
                match h with ⟨w, rpw⟩ :=
                    ⟨w, rpw hr⟩
                end ))
        (assume h : (r → ∃ x, p x),
            by_cases
                (assume hr: r,
                    have hx: ∃ x, p x, from h hr,
                    match hx with ⟨w, hpw⟩ := ⟨w, λ _, hpw⟩
                    end )
                (assume nhr: ¬r, ⟨a,(assume hr:r, absurd hr nhr)⟩))

end
--6: give a calculational proof
section
    variables (real : Type) [ordered_ring real]
    variables (log exp : real → real)
    variable  log_exp_eq : ∀ x, log (exp x) = x
    variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
    variable  exp_pos    : ∀ x, exp x > 0
    variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

    -- this ensures the assumptions are available in tactic proofs
    include log_exp_eq exp_log_eq exp_pos exp_add

    example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
    by rw [exp_add, exp_add]

    example (y : real) (h : y > 0)  : exp (log y) = y :=
    exp_log_eq h
    -- don't understand
    theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
        log (x * y) = log x + log y :=
        begin
        rw[<-exp_log_eq hx, <-exp_log_eq hy, <-exp_add],
        simp only [log_exp_eq]
        end

end

--7
--use only ring properties of ℤ in Section 4.2 + the theorem sub_self.
#check sub_self

example (x : ℤ) : 
    x * 0 = 0 :=
    by simp
-- IDK why this doesn't work
 -- rw [<-neg_add_self, sub_mul, sub_self]

end s4x

