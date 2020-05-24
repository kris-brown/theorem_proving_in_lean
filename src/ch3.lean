-- Section 3.1: Propositions as Types
namespace s31
    constant and : Prop → Prop → Prop
    constant or : Prop → Prop → Prop
    constant not : Prop → Prop
    constant implies : Prop → Prop → Prop

    variables p q r A B: Prop
    #check and p q                      -- Prop
    #check or (and p q) r               -- Prop
    #check implies (and p q) (and q p)  -- Prop


    constant Proof : Prop → Type

    constant and_comm : Π p q : Prop,
    Proof (implies (and p q) (and q p))

    #check and_comm p q      -- Proof (implies (and p q) (and q p))

    constant modus_ponens :
    Π p q : Prop, Proof (implies p q) →  Proof p → Proof q

    constant implies_intro :
    Π p q : Prop, (Proof p → Proof q) → Proof (implies p q).


end s31

-- Section 3.2: Working with P. as T.
namespace s32

    constants p q r s: Prop
    -- Similar to 'def' but for Prop, not Type
    theorem t1_ : p → q → p := λ hp : p, λ hq : q, hp
    #print t1_

    -- Written with other syntax for readability
    theorem t1' : p → q → p :=
    assume hp : p,
    assume hq : q,
    show p, from hp

    -- Can also say "lemma" instead of theorem
    lemma t1'' : p → q → p := λ hp : p, λ hq : q, hp

    -- Can also move arguments to left of colon, like with defs
    lemma t1'''  (hp : p) (hq : q):  p := hp

    axiom hp : p -- same as constant

    theorem t2' : q → p := t1' hp
    #print t2'

    -- Want our theorem to be true for any p q, not just those particular constants

    theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
    -- Apply to other constants
    #check t1 p q                -- p → q → p
    #check t1 r s                -- r → s → r
    #check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

    variable h : r → s
    #check t1 (r → s) (s → r) h  -- (s → r) → r → s

    -- Function composition says that "implies" is transitive
    theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
    assume h₃ : p,
    show r, from h₁ (h₂ h₃)

end s32

-- Section 3.3: Propositional logic
namespace s33
    variables p q r : Prop

    #check p → q → p ∧ q
    #check ¬p → p ↔ false
    #check p ∨ q → q ∨ p

    -- Conjunction
    --------------

    -- 'example' states a theorem without naming/storing it. Essentially is just a typecheck
    example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

    #check assume (hp : p) (hq : q), and.intro hp hq

    example (h : p ∧ q) : p := and.elim_left h
    example (h : p ∧ q) : q := and.elim_right h

    -- Common abbreviation for elim_left/right
    example (h : p ∧ q) : q ∧ p :=
    and.intro (and.right h) (and.left h)

    -- Anonymous constructor

    variables  (hp : p) (hq : q)
    #check (⟨hp, hq⟩ : p ∧ q)
    example : p ∧ q := (|hp, hq|) -- ascii version


    -- Dot syntax
    variable l : list ℕ

    #check list.head l
    #check l.head -- equivalent, easier to write

    -- Dot syntax for propositions
    example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩

    -- Disjunction
    --------------
    --intro
    example (hp : p) : p ∨ q := or.intro_left q hp
    example (hq : q) : p ∨ q := or.intro_right p hq
    --elim
    example (h : p ∨ q) : q ∨ p :=
    or.elim h
    (λ hp : p,
        show q ∨ p, from or.intro_right q hp)
    (assume hq : q,
        show q ∨ p, from or.intro_left p hq)

    -- intro
    example (h : p ∨ q) : q ∨ p :=
    or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)

    -- or has two constructors,so can't use anonymous constructor
    -- still write h.elim instead of or.elim h:
    example (h : p ∨ q) : q ∨ p :=
    h.elim
    (assume hp : p, or.inr hp)
    (assume hq : q, or.inl hq)


    -- Negation/falsity
    example (hpq : p → q) (hnq : ¬q) : ¬p :=
    assume hp : p,
    show false, from hnq (hpq hp)
    -- explosion (q is implicit argument in false.elim)
    example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)
    -- Shorthand for explosion
    example (hp : p) (hnp : ¬p) : q := absurd hp hnp

    -- proof of ¬p → q → (q → p) → r:


    example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

    -- Logical equivalence
    -----------------------
    theorem and_swap : p ∧ q ↔ q ∧ p :=
    iff.intro
    (assume h : p ∧ q,
        show q ∧ p, from and.intro (and.right h) (and.left h))
    (assume h : q ∧ p,
        show p ∧ q, from and.intro (and.right h) (and.left h))

    #check and_swap p q    -- p ∧ q ↔ q ∧ p

    -- Modus ponens
    variable h : p ∧ q
    example : q ∧ p := iff.mp (and_swap p q) h

end s33

-- Section 3.4: Auxiliary Subgoals
namespace s34
    variables p q : Prop

    example (h : p ∧ q) : q ∧ p :=
    have hp : p, from and.left h,
    have hq : q, from and.right h,
    show q ∧ p, from and.intro hq hp

    -- suffices for backwards reasoning from a goal
    example (h : p ∧ q) : q ∧ p :=
    have hp : p, from and.left h,
    suffices hq : q, from and.intro hq hp,
    show q, from and.right h
    -- suffices hq : q leaves us with two goals.
    --- show that it indeed suffices to show q, by proving the original goal of q ∧ p with the additional hypothesis hq : q.
    --- show q.


end s34

-- Section 3.5: Classical logic
namespace s35
    open classical
    -- Excluded middle
    variables p q : Prop
    #check em p
    -- Double negation as consequence
    theorem dne {p : Prop} (h : ¬¬p) : p :=
    or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)
    -- This allows us to construct proofs by contradiction
    example (h : ¬¬p) : p :=
    by_cases
    (assume h1 : p, h1)
    (assume h1 : ¬p, absurd h1 h)
    example (h : ¬¬p) : p :=
    by_contradiction
    (assume h1 : ¬p,
        show false, from h h1)


    example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    or.elim (em p)
    (assume hp : p,
        or.inr
        (show ¬q, from
            assume hq : q,
            h ⟨hp, hq⟩))
    (assume hp : ¬p,
        or.inl hp)

end s35

-- Section 3.6: Examples of propositional validities
namespace s36
    open classical
    -- We can use sorry or an underscore to allow us to incrementally build up a proof (with warnings, not errors) to make sure the large structure is correct before tackling subgoals.
    variables p q r : Prop

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    iff.intro
    (assume h : p ∧ (q ∨ r),
        have hp : p, from h.left,
        or.elim (h.right)
        (assume hq : q,
            show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
        (assume hr : r,
            show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
    (assume h : (p ∧ q) ∨ (p ∧ r),
        or.elim h
        (assume hpq : p ∧ q,
            have hp : p, from hpq.left,
            have hq : q, from hpq.right,
            show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
        (assume hpr : p ∧ r,
            have hp : p, from hpr.left,
            have hr : r, from hpr.right,
            show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))

    -- an example that requires classical reasoning
    example : ¬(p ∧ ¬q) → (p → q) :=
    assume h : ¬(p ∧ ¬q),
    assume hp : p,
    show q, from
    or.elim (em q)
        (assume hq : q, hq)
        (assume hnq : ¬q, absurd (and.intro hp hnq) h)

end s36

-- Exercises
namespace s3x
-- 1

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := iff.intro
    (λ hpq, and.intro hpq.right hpq.left)
    (λ hpq, and.intro hpq.right hpq.left)


example : p ∨ q ↔ q ∨ p := iff.intro
    (λ hporq, or.elim hporq
        (assume hp: p, or.inr hp)
        (assume hq: q, or.inl hq))
    (λ hqorp, or.elim hqorp
        (assume hq: q, or.inr hq)
        (assume hp: p, or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := iff.intro
    (assume hpq_r : (p ∧ q) ∧ r,
        and.intro hpq_r.left.left (and.intro hpq_r.left.right hpq_r.right))
    (assume hp_qr : p ∧ (q ∧ r),
        and.intro (and.intro hp_qr.left hp_qr.right.left) hp_qr.right.right)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := iff.intro
    (assume hpq_r : (p ∨ q) ∨ r, or.elim hpq_r
        (assume hpq: (p ∨ q), or.elim hpq
            (assume hp : p, (or.inl hp))
            (assume hq : q, or.inr (or.inl hq)))
        (assume hr : r, or.inr (or.inr hr)))
    (assume hp_qr : p ∨ (q ∨ r), or.elim hp_qr
        (assume hp : p, or.inl (or.inl hp))
        (assume hqr: (q ∨ r), or.elim hqr
            (assume hq : q, or.inl (or.inr hq))
            (assume hr : r, or.inr hr)))


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := iff.intro
(assume hpqr : p ∧ (q ∨ r),
    have hp:p, from and.left hpqr,
        show (p ∧ q) ∨ (p ∧ r), from or.elim
            (and.right hpqr)
            (assume hq : q, or.inl (and.intro hp hq))
            (assume hr : r, or.inr (and.intro hp hr)))
(assume hpqpr : (p ∧ q) ∨ (p ∧ r), or.elim hpqpr
    (assume hpq : p ∧ q, and.intro
        hpq.left
        (or.inl hpq.right))
    (assume hpr : p ∧ r, and.intro
        hpr.left
        (or.inr hpr.right)))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := iff.intro
(assume hpqr : p ∨ (q ∧ r), or.elim hpqr
    (assume hp : p, and.intro
        (or.inl hp)
        (or.inl hp))
    (assume hqr : q ∧ r, and.intro
        (or.inr hqr.left)
        (or.inr hqr.right)))
(assume hpqpr: (p ∨ q) ∧ (p ∨ r),
    show p ∨ (q ∧ r), from or.elim hpqpr.left
    (assume hp: p, or.inl hp)
    (assume hq: q,
        or.elim hpqpr.right
        (assume hp: p, or.inl hp)
        (assume hr: r, or.inr (and.intro hq hr))))


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro
(assume hpqr : p → (q → r),
    (assume hpr : p ∧ q, hpqr hpr.left hpr.right))
(assume hpqr : p ∧ q → r,
    (assume hp : p,
        (assume hq : q,
            have hpq : p ∧ q, from and.intro hp hq,
            hpqr hpq)))


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := iff.intro
(assume hpqr : (p ∨ q) → r,
    have hpr : p → r, from
        (assume hp: p, hpqr (or.inl hp)),
    have hqr : q → r, from
        (assume hq : q, hpqr (or.inr hq)),
    and.intro hpr hqr)
(assume hprqr : (p → r) ∧ (q → r),
    (assume hpq : p ∨ q, or.elim hpq
     (assume hp: p, hprqr.left hp)
     (assume hq: q, hprqr.right hq)))


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := iff.intro
(assume hnpq : ¬(p ∨ q),
    have hnp: ¬p, from
        (assume hp: p, hnpq (or.inl hp)),
    have hnq: ¬q, from
        (assume hq: q, hnpq (or.inr hq)),
    and.intro hnp hnq)
(assume hnpnq : ¬p ∧ ¬q,
    (assume hpq : p ∨ q, or.elim hpq
        (assume hp :p, hnpnq.left hp)
        (assume hq: q, hnpnq.right hq)))


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    (assume hnpnq : ¬p ∨ ¬q,
        (assume hpq : p ∧ q, or.elim hnpnq
            (assume hnp :¬p, hnp hpq.left)
            (assume hnq :¬q, hnq hpq.right)))


example : ¬(p ∧ ¬p) :=
    (assume hpnp: p ∧ ¬p, hpnp.right hpnp.left)


example : p ∧ ¬q → ¬(p → q) :=
    assume hpnq : p ∧ ¬q,
        assume hpq : p → q,
            have hp : p, from hpnq.left,
            have hq : q, from hpq hp,
            have hnq : ¬ q, from hpnq.right,
            hnq hq


example : ¬p → (p → q) :=
    assume hnp : ¬p,
    assume hp : p,
    absurd hp hnp


example : (¬p ∨ q) → (p → q) :=
    assume hnpq : ¬p ∨ q,
        assume hp : p,
        or.elim hnpq
            (assume hnp : ¬p, absurd hp hnp)
            id


example : p ∨ false ↔ p := iff.intro
(assume hpf : p ∨ false, or.elim hpf
    (assume hp : p, hp)
    (assume f: false,
    false.elim f))
(assume hp : p, or.inl hp)


example : p ∧ false ↔ false := iff.intro
(assume hpf: p ∧ false, hpf.right)
(assume hf : false, false.elim hf)


example : (p → q) → (¬q → ¬p) :=
    assume hpq : p → q,
    assume hnq : ¬q,
    assume hp : p,
    absurd (hpq hp) hnq


-- 3

--2 (use classical reasoning)
open classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    assume hprs: p → r ∨ s,
    have hpnp : p ∨ ¬ p, from em p,
    or.elim hpnp
    (assume hp : p,
        have hrs : r ∨ s, from hprs hp,
        or.elim hrs
        (assume hr : r, or.inl (assume _ : p, hr))
        (assume hs: s, or.inr (assume _ : p, hs)))
    (assume hnp : ¬ p, or.inl
        (assume hp : p, absurd hp hnp))


example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    assume hnpq : ¬(p ∧ q) ,
    have emp : p ∨ ¬p , from em p ,
    or.elim emp
    (assume hp : p,
        have emq : q ∨ ¬q , from em q ,
        or.elim emq
        (assume hq : q, absurd (and.intro hp hq) hnpq)
        (assume hnq : ¬q, or.inr hnq))
    (assume hnp : ¬p, or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
    assume h : ¬(p → q),
    have emp : p ∨ ¬p , from em p ,
    or.elim emp
        (assume hp : p,
            have emq : q ∨ ¬q , from em q ,
            or.elim emq
                (assume hq : q,
                    have imp: p → q, from (λ x: p, hq ),
                    absurd imp h)
                (assume hnq : ¬q, and.intro hp hnq))
        (assume hnp : ¬p,
            have imp : p → q, from (λ x: p, absurd x hnp),
            absurd imp h)


example : (p → q) → (¬p ∨ q) :=
    assume hpq : p → q,
    have emp : p ∨ ¬p , from em p ,
    or.elim emp
    (assume hp : p, or.inr (hpq hp))
    (assume hnp : ¬p, or.inl hnp)


example : (¬q → ¬p) → (p → q) :=
    assume hnqnp : ¬q → ¬p,
    assume hp: p,
    have emq : q ∨ ¬q , from em q ,
    or.elim emq
    id
    (assume hnq : ¬q, absurd hp (hnqnp hnq))


example : p ∨ ¬p := em p


example : (((p → q) → p) → p) :=
    assume hpqp : (p → q) → p,
    have hem : p ∨ ¬p, from em p,
    or.elim hem
        (assume hp: p, id hp)
        (assume hnp: ¬p,
            absurd
            (have hpq: p → q, from
                (assume hp: p, absurd hp hnp),
            hpqp hpq)
            hnp)



end s3x