import data.fintype.basic
import data.equiv.basic
import data.real.basic
import tactic

namespace futurama

open equiv -- "perm x" is "equiv x x" AKA "x ≃ x"
open nat
open list


/-
1. Abbreviations (could add more if needed)
-/
def finpairs (n:ℕ) : Type := list (fin n × fin n)

/-
2. Defining a predicate for a permutation on a finite set to be a k-cycle

Start at 0, and take k steps (which don't bring you to 0 until the last one)
-/
def cyclicrec : Π{n:ℕ}, ℕ → fin n → perm (fin n) → Prop
 | n 0 curr p := (p.to_fun curr).val = 0
 | n (succ m) curr  p := ((p.to_fun curr).val > 0 )
                         ∧ cyclicrec m (p.to_fun curr) p

def cyclic : Π{n:ℕ}, perm (fin n) → Prop
 | 0        _ := ff -- exclude 0-cycles
 | (succ m) p := cyclicrec m ⟨0, succ_pos'⟩ p

--instance decidable {n:ℕ} {p: perm (fin n)} : (cyclic p) := sorry

/-
3. Proposed sequence of switches to solve futurama problem for a single cycle

For an arbitrary simple cycle of length k, the sequence of switches is (specializing 'i' from the wikipedia proof to 'k-1'):
    (x, 1) (x, 2) ... (x, k-1) (y, k) (x k) (y 1) (x y)

The two additional elements x and y are represented as n+1 and n+2 respectively
-/

def construction_rec : Π{n:ℕ} {p: perm (fin n)}, ℕ → cyclic p → finpairs (n+2)
 | n p (succ m) h := (n+1, n-m-1) :: construction_rec m h
 | n _ 0        h := (n+2,n)::(n+1,n)::(n+2,1)::(n+1,n+2)::nil

def construction {n : ℕ} {p : perm (fin n)} (h: cyclic p)
    : finpairs (n+2) := construction_rec n h

/-
4. Defining a swap operation. For a perm σ, swap σ x y means:
    If a→x in σ, then a→y in the result (and vice versa)
    If x→b in σ, then y→b in the result (and vice versa)

Swapping two elements of a permutation yields a permutation.
-/


def swap' {α : Type*} [decidable_eq α] (x: α) (y: α) : α → α :=
    λ a :α, if      a = x then y
            else if a = y then x
            else               a

def swap {α : Type*} [decidable_eq α] (x: α) (y: α) : perm α :=
    ⟨swap' x y,swap' x y,
    show function.left_inverse (swap' x y) (swap' x y), by begin
        intros a,
        unfold swap', split_ifs,
            {rwa h},
            {rwa h},
            {rwa h_1},
            {refl},
    end
    ,
    show function.right_inverse (swap' x y) (swap' x y), by begin
    intros a,
    unfold swap', split_ifs,
        {rwa h},
        {rwa h},
        {rwa h_1},
        {refl},
    end
    ⟩


-- Swap a list of swaps in sequence
def swaps {α : Type*} [decidable_eq α] : perm α → list (α×α) → perm α
    | f ((a1, a2) :: b) := f * (swap a1 a2) * swaps f b
    | f nil             := f

/-
5. Defining a predicate on a list of swaps to judge whether they
   satisfy the constraints of The Prisoner of Benda

   If we have the swap (x,y) at any position in the list, we return ff
   iff (x,y) or (y,x) appears at any other point in the list.

   This is done by iterating through the list, accumulating a set of
   (ordered) pairs. For each swap we check if it (or its reverse)
   is in the seen set.
-/

def valid_swaps_rec  {α : Type*} [decidable_eq α]:
    list (α×α) → set (α×α) → Prop
| list.nil _ := tt
| ((ha,hb)::tl) seen := ¬((ha,hb) ∈ seen ∨ (hb,ha) ∈ seen)
                        ∧ (valid_swaps_rec tl (set.insert (ha,hb) seen))

def valid_swaps {α : Type*} [decidable_eq α] (s : list (α×α)) : Prop :=
    valid_swaps_rec s ∅


/-
6. Two extra elems in the set being permuted needed for the construction to work.
This function takes a permutation on n elements and extends it to a
permutation on n+2 elements.
-/

def add_two_to_perm_forward {n: ℕ} (p : perm (fin n)) : fin (n+2) → fin(n+2) :=
    λ m : fin (n+2),
        if h: m.val < n
        then have x : fin n, from p.to_fun (fin.mk m.val h),
            (fin.mk x.val (lt.trans x.is_lt (by simp only [succ_pos', lt_add_iff_pos_right])))
        else m
def add_two_to_perm_reverse {n: ℕ} (p : perm (fin n)) : fin (n+2) → fin(n+2) :=
    λ m : fin (n+2),
        if h: m.val < n
        then have x: fin n, from p.inv_fun (fin.mk m.val h),
            (fin.mk x.val (lt.trans x.is_lt (by simp only [succ_pos', lt_add_iff_pos_right])))
        else m

-- The result is still a permutation after adding
lemma a2finv {n : ℕ} (p : perm (fin n)) :
    function.left_inverse (add_two_to_perm_reverse p) (add_two_to_perm_forward p) :=
    begin
        unfold function.left_inverse,
        intros m,
        rw add_two_to_perm_forward,
        dsimp,
        cases (decidable.em (m.val < n)) with hl hg,
            {
                rw dif_pos hl,
                rw add_two_to_perm_reverse,
                dsimp,
                have t1: coe_fn (equiv.symm p) = p.inv_fun , by refl,
                have t2: coe_fn p = p.to_fun , by refl,
                rw t1, rw t2,
                rw dif_pos (p.to_fun ⟨m.val, hl⟩).is_lt,
                simp only [symm_apply_apply, fin.eta, to_fun_as_coe, inv_fun_as_coe]
            },
            {
                rw add_two_to_perm_reverse, dsimp,
                rw dif_neg hg,
                rw dif_neg hg,
            }
end
lemma a2rinv {n : ℕ} (p : perm (fin n)):
    function.right_inverse (add_two_to_perm_reverse p) (add_two_to_perm_forward p)
    :=  begin
        unfold function.right_inverse,
        intros m,
        rw add_two_to_perm_forward,
        dsimp,
        cases (decidable.em (m.val < n)) with hl hg,
            {
                rw add_two_to_perm_reverse,
                dsimp,
                rw dif_pos hl,
                have t1: coe_fn (equiv.symm p) = p.inv_fun , by refl,
                have t2: coe_fn p = p.to_fun , by refl,
                rw t1, rw t2,
                rw dif_pos (p.inv_fun ⟨m.val, hl⟩).is_lt,
                simp only [apply_symm_apply, fin.eta, to_fun_as_coe, inv_fun_as_coe],
            },
            {
                rw add_two_to_perm_reverse, dsimp,
                rw dif_neg hg,
                rw dif_neg hg,
            }
end
-- Combine the four above ingredients
def add_two {n :ℕ} (p : perm (fin n)) : perm (fin (n+2)) :=
    ⟨add_two_to_perm_forward p, add_two_to_perm_reverse p,
     a2finv p, a2rinv p⟩
/-
7. The main theorem:

Test that
    1.) the construction above returns everyone to their original bodies
        (yields the identity permutation)
and 2.) it has no repeat swaps
-/
theorem futurama_thm {n: ℕ} {p: perm (fin n)} (h: cyclic p) :
    swaps (add_two p) (construction h) = 1
    ∧ valid_swaps (construction h)
    := sorry

/-
8. Constructing+printing permutations for testing
-/
def ss_rec  : Π {n:ℕ}, list (fin n) → perm (fin n)
| _ nil         := 1
| _ (h::nil)    := 1 -- Actually this case is never encountered
| _ (h::h2::t)  := (swap h h2) * (ss_rec (h2::t))

def mk_cyclic {n:ℕ} (l : list (fin n)) : perm (fin n) := ss_rec l


def to_perm' {n : ℕ} (l : list (fin n × fin n)) : perm (fin n) :=
    swaps 1 l

def pp_rec : Π{n:ℕ}, ℕ → perm (fin n) → string
 | _ 0 _ := "|"
 | n (succ m) p := if h: m < n
                 then "|" ++ (pp_rec m p) ++ to_string m
                      ++ "→"++ (to_string (p.to_fun ⟨m, h⟩))
                 else "ERROR"

def print_perm {n:ℕ} (p:perm (fin n)) : string := pp_rec n p

end futurama