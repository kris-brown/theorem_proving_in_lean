-- Section 4.1:
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
-- Section 4.2:
namespace s42
end s42

-- Section 4.3:
namespace s43
end s43

-- Section 4.4:
namespace s44
end s44

-- Section 4.5:
namespace s45
end s45

-- Exercises
namespace s4x
end s4x
