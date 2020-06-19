import data.fintype.basic
import data.equiv.basic
import data.real.basic
import tactic

open equiv -- "perm x" is "equiv x x" AKA "x ≃ x"
open nat
open list
set_option trace.simplify.rewrite false

-- Repeat a binary function n times
def rep {α : Type*} : ℕ → (α → α) → α → α
 | zero     _ x := x
 | (succ n) f x := f (rep n f x)

-- Predicate for a permutation on a finite set to be cyclic
-- Any element should work - ∃ is to avoid empty finite set

def cyclic' {n : ℕ} (p : perm (fin n)) (x: fin n) :=
    rep n p.to_fun x = x

def cyclic  : Π{n:ℕ}, perm (fin n) → Prop
   | 0  _ := ff
   | (succ m) p := cyclic' p (fin.mk 0 (by simp only [succ_pos']))


-- Proposed sequence of switches to solve futurama problem for a single cycle

--Helper recursive function
def construction_rec : Π{n:ℕ} {p: perm (fin n)},
                       bool → ℕ → cyclic p → list ((fin (n+2)) × (fin (n+2)))
 | _ _ tt 0        h := construction_rec ff 0 h
 | _ _ ff 0        _ := list.nil
 | n p ff (succ m) h := (n+1,succ m) :: construction_rec tt m h
 | n p tt (succ m) h := (n+1,succ m) :: construction_rec tt m h

def construction {n : ℕ} {p : perm (fin n)} (h: cyclic p)
    : list ((fin (n+2)) × (fin (n+2)))
    := construction_rec ff n h


-- identity permutation for arbitrary type
def id_perm (α : Type*) : perm α := ⟨id, id,
                                     by {intro _, refl}, by {intro _, refl}⟩


-- Helpers for swap, defined below
-- Swapping two elements of a permutation yields a permutation
lemma perm_swap {α β : Type*} (c: α ≃ β) (a: α) (b : β):
        c.to_fun a = b ↔ c.inv_fun b = a := iff.intro
    (assume h : c.to_fun a = b, by
        calc
        c.inv_fun b = c.inv_fun (c.to_fun a)  : congr_arg c.inv_fun (eq.symm h)
                ... = a :  by rw c.left_inv)
    (assume h : c.inv_fun b = a,
        calc c.to_fun a = c.to_fun (c.inv_fun b) : congr_arg c.to_fun (eq.symm h)
                    ... = b : by rw c.right_inv)



def swapf {α : Type*} [decidable_eq α] (f: perm α) (x: α) (y: α) : α → α :=
    λ a :α, if      a = x then f.to_fun y
            else if a = y then f.to_fun x
            else               f.to_fun a
def swapr {α : Type*} [decidable_eq α] (f: perm α) (x: α) (y: α) : α → α :=
    λ fa: α, if      f.inv_fun fa = x then y
             else if f.inv_fun fa = y then x
             else                          f.inv_fun fa

def swap {α : Type*} [decidable_eq α] (f: perm α) (x: α) (y: α) : perm α :=
    ⟨swapf f x y, swapr f x y,
    show function.left_inverse (swapr f x y) (swapf f x y), by begin
        intros a,
        unfold swapr, unfold swapf,
        split_ifs,
            {rw f.left_inv at h_1, rwa h},
            {exact eq.symm h},
            {rw f.left_inv at h_2, contradiction},
            {exact eq.symm h_1},
            {rw f.left_inv at h_2, contradiction},
            {rw f.left_inv at h_2, contradiction},
            {rw f.left_inv at h_2, contradiction},
            {rw f.left_inv at h_3, contradiction},
            {rw f.left_inv}
        end ,
    show function.right_inverse (swapr f x y) (swapf f x y), by begin
        intros a,
        unfold swapr, unfold swapf,
        split_ifs,
            {rw <-(perm_swap f x a) at h,
             rwa <-h_1 at h},
             {rwa (perm_swap f x a)},
             {rwa (perm_swap f y a)},
             {rwa f.right_inv}
        end
    ⟩

def swaps {α : Type*} [decidable_eq α] : perm α → list (α×α) → perm α
    | f ((a1, a2) :: b) := swaps (swap f a1 a2) b
    | f nil             := f

-- Never swap the same pair twice
def valid_swaps_rec  {α : Type*} [decidable_eq α]:
    list (α×α) → set (α×α) → Prop
| list.nil _ := tt
| ((ha,hb)::tl) seen := ¬((ha,hb) ∈ seen ∨ (hb,ha) ∈ seen)
                        ∧ (valid_swaps_rec tl (set.insert (ha,hb) seen))

-- Top level call to check that the list of swaps is valid
def valid_swaps {α : Type*} [decidable_eq α] (s : list (α×α)) : Prop :=
    valid_swaps_rec s ∅



-- Two extra elems in the set being permuted needed for the construction to work.
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

-- Test that 1.) the construction returns everyone to their original bodies
-- (yields the identity permutation) and 2.) it has no repeat swaps
theorem futurama {n: ℕ} {p: perm (fin n)} (h: cyclic p) :
    swaps (add_two p) (construction h) = id_perm (fin (n+2))
    ∧ valid_swaps (construction h)
    := sorry

