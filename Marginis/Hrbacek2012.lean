/-
Copyright (c) 2025 Kelly Masaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Masaki
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Tactic
import Mathlib.Logic.Basic

/-!
# Relative set theory: Strong stability by Karel Hrbacek (2012)
http://logicandanalysis.org/index.php/jla/article/view/158
## Important Axioms:
-/

/--Relativization
   o-/
lemma o (t : Type) : ∀ U V : Set t,
    (∀ x, x ∈ U ↔ x ∈ V) → U = V := by
        exact fun U V a ↦ Set.ext a

/--i-/
lemma i (t : Type) : ∀ x : t, ∃ V : Set t,
    x ∈ V ∧ ∀ (U : Set t), x ∈ U → V ⊆ U := by
        intro x
        use {x}
        constructor
        · simp
        · simp

/--ii-/
lemma ii : ∃ t : Type, ¬(∀ V : Set (Set t),
    ∅ ∈ V ∧ ∃x ∈ V, ∀ U : Set (Set t), (x ∈ U → V ⊆ U)) := by
        push_neg
        use ℕ
        use {{1,2},{3,4}}
        intro h
        simp_all
        exfalso
        cases h with
            | inl h_1 =>
                have t1 : 1 ∈ ({1,2} : Set ℕ) := by
                    simp_all
                rw[←h_1] at t1
                simp at t1
            | inr h_2 =>
                have t2 : 3 ∈ ({3,4} : Set ℕ) := by
                    simp_all
                rw[←h_2] at t2
                simp at t2

/--iii-/
lemma iii : ∃ t : Type, ¬ ∀ U V : Set t, U ⊆ V ∨ V ⊆ U := by
    use ℕ
    push_neg
    use {2}
    use {3}
    simp

/--iv-/
lemma iv : ∀t : Type, ¬(∀U : Set t, ∃V : Set t, (U ⊂ V)) := by
    intro t
    push_neg
    use Set.univ
    intro V
    exact not_ssubset_of_subset fun ⦃a⦄ a ↦ trivial

/--v-/
lemma v (t : Type)(a : t) : ¬(∀ U V : Set t, U ⊂ V → ∃W : Set t, U ⊂ W ∧ W ⊂ V):= by
    push_neg
    use ∅
    use {a}
    simp
    refine fun W hw ↦ ?_
    intro hw1
    have : ∃b : t, b ∈ W := by aesop
    obtain ⟨c, h1⟩ := this
    have := hw1.1 h1
    have := hw1.2
    aesop

/-- A set L is a level set if for all x,y is an element of L V(x) = V(y) implies x = y.
Level sets are finite, and the relation v defined on L by x ⊑ y $ V(x) ⊆ V(y) is a wellordering.
We always describe level sets in the increasing order by ⊑,
if L = {z₀; z₁; ... ; zₗ} is a level set, then V(z₀) ⊂ V(z₁) ⊂ ... ⊂ V(zₗ).-/
def one (t : Type)(L : Set t)(V : t → Set t) :=
    ∀ x ∈ L, ∀ y ∈ L, (V x = V y → x = y)

/--Let L be a level set. We write V ≅_L V' if V ⊆ V(z) <-> V' ⊆ V(z) and V(z) ⊆ V <-> V(z) ⊆ V' hold for all z elements of L.
Either V = V₀ = V(z₀) for some j ≤ l,
or V, V' ⊂ V(z₀),
or V(zⱼ) ⊂ V, V' ⊂ V(zⱼ₊₁) for some j < l,
or V(zₗ) ⊂ V; V'
Therefore ≅_L classifies all levels into 2l + 3 classes-/
def two (t : Type)(L V₀ V₁ : Set t)(V : t → Set t) :=
    ∀ z ∈ L, (V₀ ⊆ V z ↔ V₁ ⊆ V z) ∧ (V z ⊆ V₀ ↔ V z ⊆ V₁)

theorem twoholdsifsame  (t : Type)(L V₀ : Set t)(V : t → Set t) :
  two t L V₀ V₀ V := by
    intro z
    intro h
    constructor
    · simp
    · simp
