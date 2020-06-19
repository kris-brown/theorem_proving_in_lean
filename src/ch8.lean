
-- Section 8.1: pattern matching
namespace s81
open nat

def sub1 : ℕ → ℕ
| zero     := zero
| (succ x) := x

def is_zero : ℕ → Prop
| zero     := true
| (succ x) := false

example : sub1 0 = 0 := rfl
example (x : ℕ) : sub1 (succ x) = x := rfl

example : is_zero 0 = true := rfl
example (x : ℕ) : is_zero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : ℕ) : ¬ is_zero (x + 3) := not_false

end s81
-- Section 8.2: wildcards/overlapping patterns
namespace s82
end s82
-- Section 8.3: structural recursion
namespace s83
end s83
-- Section 8.4: Well-founded recursion
namespace s84
end s84
-- Section 8.5: Mutual recursion
namespace s85
end s85
-- Section 8.6: Dependent pattern matching
namespace s86
end s86
-- Section 8.7: Inaccessible terms
namespace s87
end s87
-- Section 8.8: Match expressions
namespace s88
end s88
-- Exercises
namespace s8x
end s8x