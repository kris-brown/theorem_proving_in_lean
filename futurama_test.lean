import data.equiv.basic
import data.real.basic
import data.list.nodup
import group_theory.perm.sign
import group_theory.perm.cycles
import futurama

open classical function
open futurama
open equiv

/-
Unit tests for methods in futurama namespace
-/


-- Examples

def V4 : S[4] := swaps [(1, 0), (2, 3)] -- Klein 4 group
def Z3 : S[3] := swaps [(1, 0), (2, 1)] -- ℤ/3ℤ
def Z4 : S[4] := mk_cyclic [0, 1, 2, 3]    -- ℤ/4ℤ
def Z5 : S[5] := mk_cyclic [0, 1, 2, 3, 4]    -- ℤ/5ℤ
def C5 : S[5] := mk_cyclic [0, 1, 3, 4, 2]    -- ℤ/5ℤ
def Z3' : S[5] := add_two Z3
def Z4' : S[6] := add_two Z4
def Z5' : S[7] := add_two Z5
def C5' : S[7] := add_two C5

#eval print_perm $ Z3
#eval print_perm $ V4
#eval print_perm $ Z4
#eval print_perm $ Z5
#eval print_perm $ C5


-- Test 1: Misc tests: Klein 4 V
example : (print_perm (V4 * V4) = print_perm (1: perm (fin 4))) := by refl

-- Test 2: cyclic predicate
#eval  cyclic V4 -- ff
#eval  cyclic Z4 -- tt

-- Test 3: construction
#eval print_perm $ swaps (construction Z3)
-- compare to the wiki proof, should be
-- [(x, 1), (x, 2), (y, 3), (x, 3), (y, 1), (x, y)]         (1-indexed, x=k+1, y=k+2)
-- aka [(3, 0), (3, 1), (4, 2), (3, 2), (4, 0), (3, 4)]
#eval print_finpairs$ construction Z5
-- Test 4: swap
example : print_perm (equiv.swap (1: fin 4) (2: fin 4)) = "|0→0|1→2|2→1|3→3|" := by refl


-- Test 5: Valid swaps
#eval valid_swaps [(3, 0), (3, 1), (4, 2), (3, 2), (4, 0), (3, 4)] -- tt
#eval valid_swaps [(3, 0), (3, 1), (4, 2), (3, 2), (4, 0), (0, 3)] -- ff: 3,0 and 0,3

-- Test 6: add two
example : print_perm (add_two V4) = "|0→1|1→0|2→3|3→2|4→4|5→5|" := by refl

-- Test 7:
#eval print_perm (Z4' * ((swaps  (construction Z4))))
#eval print_perm (Z3' * ((swaps  (construction Z3))))
#eval print_perm (C5' * ((swaps  (construction C5))))
#eval valid_swaps (construction Z4)

instance fin.inhabited {n:ℕ}: inhabited (fin (nat.succ n)) := ⟨⟨0, nat.succ_pos'⟩⟩


-- Library func can decompose arbitrary perm into disjoint cycles

#eval list.length (perm.cycle_factors V4).1.tail
#check (perm.cycle_factors V4).property


#eval (1::1::list.nil).nodup