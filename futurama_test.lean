import data.equiv.basic

import futurama

open futurama
open equiv

/-
Unit tests for methods in futurama namespace
-/


-- Examples

def V4 : perm (fin 4) := to_perm' [(1, 0), (2, 3)] -- Klein 4 group
def Z3  : perm (fin 3)   := to_perm' [(1, 0), (2, 1)] -- ℤ/3ℤ


#eval print_perm $ Z3
#eval print_perm $ V4

-- Test 2: cyclic predicate
example : cyclic V4 := by sorry


example : print_perm (add_two V4) = "0→1|1→0|2→3|3→2|4→4|5→5|" := by refl
-- Test 1: Misc tests: Klein 4 V
example : (print_perm (V4 * V4) = print_perm (1: perm (fin 4))) := by refl