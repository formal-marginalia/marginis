import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!

# Representation of Integers: A nonclassical point of view

[Bellaouar Djamel, Boudaoud Abdelmadjid 2020](http://logicandanalysis.org/index.php/jla/article/view/4)

In the Introduction,
this paper defines functions ω and Ω which give the number of distinct prime divisors
and the total number of prime factors of a number.
We define these and calculate some examples.

-/

def Ω (n:ℕ) : ℕ := (Nat.primeFactorsList n).length
open Finset
def ω (n : ℕ) := card (filter (fun p : Fin (n.succ) ↦ Nat.Prime p ∧ padicValNat p n > 0) univ)

#eval ω 12

#eval Ω 12

#eval Nat.primeFactorsList 6


-- example : Nat.primeFactorsList 6 = [2,3] := by
--   decide

#eval Nat.primeFactorsList 1001

#eval padicValNat 2 16777216

#eval padicValNat 5 10

-- example : List.Perm [3,2] (Nat.primeFactorsList 6) := by decide

example : 24 ≤ padicValNat 2 16777216 ↔ (List.replicate 24 2).Subperm
  (Nat.primeFactorsList 16777216) :=
    le_padicValNat_iff_replicate_subperm_primeFactorsList
      Nat.prime_two <|Ne.symm <|Nat.zero_ne_add_one 16777215

-- example : (List.replicate 4 2).Subperm
--   (Nat.primeFactorsList 16) := by decide
