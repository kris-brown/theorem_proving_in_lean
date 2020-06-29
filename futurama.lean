import data.fintype.basic
import data.equiv.basic
import data.real.basic
import algebra.group.defs
import tactic

-- https://en.wikipedia.org/wiki/The_Prisoner_of_Benda#The_theorem


-- Perhaps this could be improved by using more from:
 --https://leanprover-community.github.io/mathlib_docs/group_theory/perm/sign.html#equiv.perm.is_cycle

-- Though this (more general) permutation infrastucture is often not decidable
namespace futurama

open equiv -- "perm x" is "equiv x x" AKA "x ≃ x"
open nat
open list


/-
1. Abbreviations (could add more if needed)
-/
@[reducible] def finpairs (n:ℕ) : Type := list (fin n × fin n)
notation `S[` n `]`  := perm (fin n) -- symmetric group on n elements

/-
2. Defining a predicate for a permutation on a finite set to be a k-cycle
Start at 0, and take k steps (which don't bring you to 0 until the last one)
-/
def cyclicrec : Π{n:ℕ}, ℕ → fin n → perm (fin n) → bool
 | n 0 curr p := (p.to_fun curr).val = 0
 | n (succ m) curr  p := ((p.to_fun curr).val > 0 )
                         ∧ cyclicrec m (p.to_fun curr) p

def cyclic : Π{n:ℕ}, perm (fin n) → bool
 | 0        _ := ff -- exclude 0-cycles
 | (succ m) p := cyclicrec m ⟨0, succ_pos'⟩ p


/-
3. Proposed sequence of switches to solve futurama problem for a single cycle

For an arbitrary simple cycle of length k, the sequence of switches is (specializing 'i' from the wikipedia proof to '1'):
    (x, 1) (y, 2) ... (y, k) (x k) (y 1)
or, for any simple cycle with an element 'a':
    (x, a) (y p¹a) ... (y pᵏ⁻¹ a)  (x pᵏ⁻¹ a) (y a)

The two additional elements x and y are represented as n and n+1 respectively
(elements within the set are 0,1,...,n-1).
-/


def construction_rec : Π{n:ℕ} , ℕ → fin n → S[n] → finpairs (n+2)
 | n (succ counter) curr p := (n+1,p.to_fun curr)
                              :: construction_rec counter (p.to_fun curr) p
 | n 0              _    _ := (n,1)::(n+1,0)::(n,n+1)::nil

def construction : Π{n : ℕ}, S[n] → finpairs (n+2)
 | 0        _ := nil
 | (succ m) p := (succ m, 0) :: construction_rec m ⟨0, succ_pos'⟩ p

def construction_rec' : Π{n:ℕ} , ℕ → fin n → S[n] → finpairs (n+2)
 | n (succ counter) curr p := (n+1,p.to_fun curr)
                              :: construction_rec counter (p.to_fun curr) p
 | n 0              _    _ := (n,1)::(n+1,0)::(n,n+1)::nil

def construction' : Π{n : ℕ}, S[n] → finpairs (n+2)
 | 0        _ := nil
 | (succ m) p := (succ m, 0) :: construction_rec m ⟨0, succ_pos'⟩ p


/-
4. For a perm σ, equiv.swap σ x y means:
    If a→x in σ, then a→y in the result (and vice versa)
    If x→b in σ, then y→b in the result (and vice versa)

Defining the application of a list of swaps in sequence
-/

--
def swaps {α : Type*} [decidable_eq α] : list (α×α) → perm α
    | ((a1, a2) :: b) := (equiv.swap a1 a2) * swaps b
    | nil             := 1

/-
5. Defining a predicate on a list of swaps to judge whether they
   satisfy the constraints of The Prisoner of Benda

   If we have the swap (x,y) at any position in the list, we fail
   iff (x,y) or (y,x) appears at any other point in the list.

   This is done by iterating through the list, accumulating a set of
   (ordered) pairs. For each swap we check if it (or its reverse)
   is in the seen set.
-/

def valid_swaps_rec  {α : Type*} [decidable_eq α]:
    list (α×α) → finset (α×α) → bool
| list.nil      _    := tt
| ((ha,hb)::tl) seen := ¬((ha,hb) ∈ seen ∨ (hb,ha) ∈ seen)
                        ∧ (valid_swaps_rec tl (insert (ha,hb) seen))

def valid_swaps {α : Type*} [decidable_eq α] (s : list (α×α)) : bool :=
    valid_swaps_rec s ∅


/-
6. Two extra elems in the set being permuted needed for the construction to work.
This function takes a permutation on n elements and extends it to a
permutation on n+2 elements.
-/

def add_two_to_perm_forward {n: ℕ} (p : S[n]) : fin (n+2) → fin(n+2) :=
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

def futurama_correct  {n: ℕ} {p: S[n]} (h: cyclic p) :
    (add_two p) * swaps (construction p) = 1:= begin
    induction n with k ih,
    { --trivial n=0 case
        unfold construction,
        unfold swaps,
        apply one_mul
    },
    {--n>0
        ext,
        rw perm.one_apply,
        rw perm.mul_apply,
        unfold construction,
        rw cast_succ,
        induction x with k2 ih2,
        simp only [],

        --cases (decidable.em (k2 < k)) with hl hg,

        --squeeze_simp,
        --unfold swaps,
        --unfold add_two,
        --unfold add_two_to_perm_forward,
        --unfold add_two_to_perm_reverse,
        sorry,
    },
end


def futurama_valid  {n: ℕ} {p: S[n]} (h: cyclic p) :
    valid_swaps (construction p) := begin
    induction n with k ih,
    { -- trivial n=0 case
         unfold construction,
         unfold valid_swaps,
         unfold valid_swaps_rec,
         trivial

    },
    {
        unfold construction,
        unfold valid_swaps,
        induction p,

        sorry}
end

theorem futurama_thm {n: ℕ} {p: S[n]} (h: cyclic p) :
    (add_two p) * swaps (construction p) = 1
    ∧ valid_swaps (construction p)
    := ⟨futurama_correct h, futurama_valid h⟩


/-
8. Constructing+printing permutations for testing
-/
-- Make a simple cycle from a list, e.g. [2, 1, 3, 0]
def ss_rec  : Π {n:ℕ}, list (fin n) → perm (fin n)
| _ nil         := 1
| _ (h::nil)    := 1 -- Actually, this case is never encountered
| _ (h::h2::t)  := (swap h h2) * (ss_rec (h2::t))

def mk_cyclic {n:ℕ} (l : list (fin n)) : S[n] := ss_rec l

-- Show where each permuted element goes to
def pp_rec : Π{n:ℕ}, ℕ → S[n] → string
 | _ 0 _ := "|"
 | n (succ m) p := if h: m < n
                   then (pp_rec m p) ++ to_string m ++"→"++
                        (to_string (p.to_fun ⟨m, h⟩)) ++ "|"
                   else "ERROR"

def print_perm {n:ℕ} (p: S[n]) : string := pp_rec n p

-- Convert the (fin n) pairs to something that Lean can represent
def print_finpairs :  Π {n:ℕ}, list (fin n × fin n) → list (ℕ×ℕ)
  | _ nil    := nil
  | n (h::t) := (h.1.val,h.2.val)::(print_finpairs t)

end futurama
