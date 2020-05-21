
-- Section 2.1: Simple type theory
namespace s21
    /- declare some constants -/

    constant m : nat        -- m is a natural number
    constant n : nat
    constants b1 b2 : bool  -- declare two constants at once

    /- check their types -/

    #check m            -- output: nat
    #check n
    #check n + 0        -- nat
    #check m * (n + 0)  -- nat
    #check b1           -- bool
    #check b1 && b2     -- "&&" is boolean and
    #check b1 || b2     -- boolean or
    #check tt           -- boolean "true"


    constant f : nat → nat           -- type the arrow as "\to" or "\r"
    constant f' : nat -> nat         -- alternative ASCII notation
    constant f'' : ℕ → ℕ             -- alternative notation for nat
    constant p : nat × nat           -- type the product as "\times"
    constant q : prod nat nat        -- alternative notation
    constant g : nat → nat → nat
    constant g' : nat → (nat → nat)  -- has the same type as g!
    constant h : nat × nat → nat

    constant F : (nat → nat) → nat   -- a "functional"

    #check f               -- ℕ → ℕ
    #check f n             -- ℕ
    #check g m n           -- ℕ
    #check g m             -- ℕ → ℕ
    #check (m, n)          -- ℕ × ℕ
    #check p.1             -- ℕ
    #check p.2             -- ℕ
    #check (m, n).1        -- ℕ
    #check (p.1, n)        -- ℕ × ℕ
    #check F f             -- ℕ
end s21

-- Section 2.2: Types as Objects
namespace s22 
    -- Going beyond simple types 
    #check nat               -- Type
    #check bool              -- Type
    #check nat → bool        -- Type
    #check nat × bool        -- Type
    #check nat → nat         -- ...
    #check nat × nat → nat
    #check nat → nat → nat
    #check nat → (nat → nat)
    #check nat → nat → bool
    #check (nat → nat) → nat
    -- Declare constants/constructors for types 
    constants α β : Type
    constant F : Type → Type
    constant G : Type → Type → Type

    #check α        -- Type
    #check F α      -- Type
    #check F nat    -- Type
    #check G α      -- Type → Type
    #check G α β    -- Type
    #check G α nat  -- Type


    #check prod α β       -- Type
    #check prod nat nat   -- Type
    #check list α    -- Type
    #check list nat  -- Type

    -- Infinite hierarchy of types
    #check Type      -- Type 1
    #check Type 0    -- Type 1
    #check Type 1   -- Type 2
    #check Type 2   -- Type 3
    #check Type 3   -- Type 4
    #check Type 4   -- Type 5

    -- Has special properties
    #check Prop -- Type

    -- Polymorphic types
    #check list    -- Type u_1 → Type u_1

    #check prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)

    universe u
    constant αα : Type u
    #check αα 

end s22

-- Section 2.3: Function abstraction and evaluation
namespace s23
    #check fun x : nat, x + 5
    #check λ x : nat, x + 5
    -- more abstract examples
    constants α β  : Type
    constants a1 a2 : α
    constants b1 b2 : β

    constant f : α → α
    constant g : α → β
    constant h : α → β → α
    constant p : α → α → bool

    #check fun x : α, f x                      -- α → α
    #check λ x : α, f x                        -- α → α
    #check λ x : α, f (f x)                    -- α → α
    #check λ x : α, h x b1                     -- α → α
    #check λ y : β, h a1 y                     -- β → α
    #check λ x : α, p (f (f x)) (h (f a1) b2)  -- α → bool

    -- Due to type inference, these next three things are all the same
    #check λ x : α, λ y : β, h (f x) y         -- α → β → α
    #check λ (x : α) (y : β), h (f x) y        -- α → β → α
    #check λ x y, h (f x) y                    -- α → β → α


    constant b : β
    -- Identity function
    #check λ x : α, x        -- α → α
    -- Constant function
    #check λ x : α, b        -- α → β
    -- Composition
    #check λ x : α, g (f x)  -- α → γ
    #check λ x, g (f x)

    -- Multiple arguments 
    constants γ : Type

    #check λ b : β, λ x : α, x     -- β → α → α
    #check λ (b : β) (x : α), x    -- β → α → α
    #check λ (g : β → γ) (f : α → β) (x : α), g (f x)
                                -- (β → γ) → (α → β) → α → γ


    -- Abstract over type 
    #check λ (α β : Type) (b : β) (x : α), x
    #check λ (α β γ : Type) (g : β → γ) (f : α → β) (x : α), g (f x)


    constants (a : α) 
    constant e : α → β 
    constant y : β → γ 
    constant w : α → α


    #check (λ x : α, x) a                -- α
    #check (λ x : α, b) a                -- β
    #check (λ x : α, b) (w a)            -- β
    #check (λ x : α, y (e x)) (w (w a))  -- γ

    #check (λ (v : β → γ) (u : α → β) x, v (u x)) y e a   -- γ

    #check (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q),
            v (u x)) α β γ y e a        -- γ


    -- Evaluate the function (beta reduction)
    #reduce (λ x : α, x) a                -- a
    #reduce (λ x : α, b) a                -- b
    #reduce (λ x : α, b) (w a)            -- b
    #reduce (λ x : α, y (e x)) a          -- g (f a)

    #reduce (λ (v : β → γ) (u : α → β) x, v (u x)) y e a   -- g (f a)

    #reduce (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q),
        v (u x)) α β γ y e a        -- g (f a)

    -- "reducing pairs"
    constants m n : nat
    constant A : bool
    #reduce (m, n).1        -- m
    #reduce (m, n).2        -- n

    -- "reducing boolean expressions"
    #reduce tt && ff        -- ff
    #reduce ff && A         -- ff
    #reduce A && ff         -- bool.rec ff ff b
    -- WARNING This last one doesn't seem to work... 

    -- "reducing arithmetic expressions"
    #reduce n + 0           -- n
    #reduce n + 2           -- nat.succ (nat.succ n)
    #reduce 2 + 3           -- 5

    -- evaluating (less trustworthy, more efficient)
    #eval 12345 * 54321

end s23

-- Section 2.4: Introducing Definitions
namespace s24
    -- one way to define new objects
    def foo : (ℕ → ℕ) → ℕ := λ f, f 0

    #check foo    -- (ℕ → ℕ) → ℕ
    #print foo    -- λ (f : ℕ → ℕ), f 0

    -- type inferred (though it's preferable to provide it)
    def foo' := λ f:(ℕ → ℕ), f 0 
    #check foo'

    -- Alternative syntax for declaring function type
    def double (x : ℕ) : ℕ := x + x
    #print double
    #check double 3
    #reduce double 3    -- 6

    def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

    #reduce do_twice double 2    -- 8

    def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) :
    γ :=
    g (f x)
    #check compose


end s24

-- Section 2.5: Local definitions
namespace s25 

    #check let y := 2 + 2 in y * y   -- ℕ
    #reduce  let y := 2 + 2 in y * y   -- 16

    def t (x : ℕ) : ℕ :=
    let y := x + x in y * y

    #reduce t 2   -- 16

    -- Let a:= t1 in t2 is DIFFERENT from (λa, t2) t1
    def foo := let a := nat  in λ x : a, x + 2
    #check foo
    /-
    def bar := (λ a, λ x : a, x + 2) nat

    This doesn't typecheck because "a" can be any type, whereas x+2 does not make sense for 
    all types. The 'let' construct is a STRONGER means of abbreviation;
    -/

end s25

-- Section 2.6 Variables and Sections 
namespace s26
    -- In general, not good practice to declare constants, we want to be constructive

    -- Tedious to specify type variables as proper variables with every declaration, so this syntax makes it easier:
    section variable_demo
        variables (β α γ : Type)
        def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
        def do_twice (h : α → α) (x : α) : α := h (h x)
        def do_thrice (h : α → α) (x : α) : α := h (h (h x))
        -- Lean automatically can add whichever variables were actually used as additional parameters
        def isnonzero(n:nat) : bool := n > 0
        def nott(b:bool) : bool := ¬b
        def iszero := compose bool ℕ bool nott isnonzero -- order of hidden parameters seems to be determined by their original declaration order 
    end variable_demo -- These declarations can be limited to sections
    -- Sections do not have to have a name
end s26

-- Section 2.7 Namespaces
namespace s27
    -- Refer to things in another namespace 
    #reduce s26.iszero 0

    -- Open up a namespace  (stays open until end of current namespace)
    open s26 
    #check do_twice

end s27

-- Section 8: Dependent types
namespace s28
    namespace hidden -- avoid conflicting with the standard library

    universe u

    constant list   : Type u → Type u

    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant head   : Π α : Type u, list α → α
    constant tail   : Π α : Type u, list α → list α
    constant append : Π α : Type u, list α → list α → list α

    variable  α : Type
    variable  a : α
    variables l1 l2 : list α

    #check cons α a (nil α)
    #check append α (cons α a (nil α)) l1
    #check append α (append α (cons α a (nil α)) l1) l2

    end hidden
    open list

    #check list     -- Type u_1 → Type u_1

    #check @cons    -- Π {α : Type u_1}, α → list α → list α
    #check @nil     -- Π {α : Type u_1}, list α
    #check @head    -- Π {α : Type u_1} [_inst_1 : inhabited α], list α → α
    #check @tail    -- Π {α : Type u_1}, list α → list α
    #check @append  -- Π {α : Type u_1}, list α → list α → list α

    universe u
    constant vec : Type u → ℕ → Type u

    namespace vec
    constant empty : Π α : Type u, vec α 0
    constant cons :
        Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
    constant append :
        Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
    end vec
    variable α : Type
    variable β : α → Type
    variable a : α
    variable b : β a

    #check sigma.mk a b      -- Σ (a : α), β a
    #check (sigma.mk a b).1  -- α
    #check (sigma.mk a b).2  -- β (sigma.snd (sigma.mk a b))

    #reduce  (sigma.mk a b).1  -- a
    #reduce  (sigma.mk a b).2  -- b

end s28

-- Section 9: Implicit Variables 
namespace s29 
    namespace hidden
    universe u
    constant list : Type u → Type u

    namespace list
        constant cons   : Π α : Type u, α → list α → list α
        constant nil    : Π α : Type u, list α
        constant append : Π α : Type u, list α → list α → list α

        variable  α : Type
        variable  a : α
        variables l1 l2 : list α

        -- This is "tedious"
        #check cons α a (nil α)
        #check append α (cons α a (nil α)) l1
        #check append α (append α (cons α a (nil α)) l1) l2

        -- We can use "implicit argument" to tell Lean to infer
        #check cons _ a (nil _)
        #check append _ (cons _ a (nil _)) l1
        #check append _ (append _ (cons _ a (nil _)) l1) l2

    end list
    -- Even implicit arguments are tedious, so make some variables implicit by default with curly braces
    namespace list2
        constant cons   : Π {α : Type u}, α → list α → list α
        constant nil    : Π {α : Type u}, list α
        constant append : Π {α : Type u}, list α → list α → list α


        variable  α : Type
        variable  a : α
        variables l1 l2 : list α

        #check cons a nil
        #check append (cons a nil) l1
        #check append (append (cons a nil) l1) l2
    end list2


    def ident {α : Type u} (x : α) : α := x

    variables α β : Type u
    variables (a : α) (b : β)

    #check ident      -- ?M_1 → ?M_1
    #check ident a    -- α
    #check ident b    -- β

    end hidden

    -- Same way of defining ident above using variables instead of curly braces
    universe u

    section
    variable {α : Type u}
    variable x : α
    def identi := x
    end

    variables α β : Type u
    variables (a : α) (b : β)

    #check identi
    #check identi a
    #check identi b

    -- Numbers are overloaded, default to Nats 
    #check 2            -- ℕ
    #check (2 : ℕ)      -- ℕ
    #check (2 : ℤ)      -- ℤ

    -- When we want to override implicit-as-default, preface with @
    #check @id        -- Π {α : Type u_1}, α → α
    #check id α       -- Type u
    #check @id α      -- α → α   
    #check @id β      -- β → β
    #check @id α a    -- α
    #check @id β b    -- β
    --#check id α a    -- ERROR
end s29

-- Section 10: Exercises 
namespace s2x
-- Ex 1. applies its argument twice, so that Do_Twice do_twice is a function that applies its input four times
def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := 
    λ (g :(ℕ → ℕ) → (ℕ → ℕ)) (f : (ℕ → ℕ)) x:ℕ, 
    g(g(f)) x
#reduce Do_Twice s24.do_twice s24.double 2

-- Ex 2. 
def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a:α) (b:β), f (a, b) 
#check curry
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ (ab:α×β), f ab.1 ab.2
#check uncurry

def add(p:ℕ) (q:ℕ) : ℕ := p+q
#reduce uncurry ℕ ℕ ℕ add (4,2)

-- Ex 3. 
-- could represent a function that adds two vectors of natural numbers of the same length
universe u 
constant vec : Π {α : Type u}, ℕ → α 

constant empty : vec 0
constant cons :
    Π (β : Type u) (n : ℕ), β → vec n → vec (n + 1)

#check cons
constant append :
    Π (α : Type u) (n m : ℕ),  vec m → vec n → vec (n + m)
constant vec_add : Π {n:ℕ}, s28.vec ℕ n → s28.vec ℕ n → s28.vec ℕ n
-- can represent a function that reverses its argument
constant vec_reverse : Π {n:ℕ}, s28.vec ℕ n → s28.vec ℕ n

variable  α : Type
variable  a : α
variables l1 l2 : list α

#check vec_add (s28.vec.empty _) (s28.vec.empty _) -- add < > < >
#check vec_add (s28.vec.cons _ _ 1 (s28.vec.empty _)) (s28.vec.cons _ _ 3 (s28.vec.empty _)) -- add <1> <3>
#check vec_reverse (s28.vec.cons _ _ 3 (s28.vec.empty _))

-- Ex 4. Declare m x n matrices

constant mat : Π {α : Type u}, ℕ → ℕ → α
constant emptyM : mat 0 0
constant vcat : Π {n m o:ℕ}, vec o → mat n m → mat (n+o) m
constant hcat : Π {n m o:ℕ}, vec o → mat n m → mat n (m+o)
constant matmul: Π {n m o:ℕ},  mat n m → mat m o → mat n o
constant matadd: Π {n m:ℕ},  mat n m → mat n m → mat n m
constant matvecmul: Π {n m:ℕ},  mat n m → vec m  → vec n

variables x y z : ℕ
constant vx : vec x
constant vy : vec y

end s2x
