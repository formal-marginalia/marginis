/-
Copyright (c) 2025 Sakura Takahashi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sakura Takahashi
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Bornology
import Mathlib.Topology.Perfect

/-!
# More reverse mathematics of the Heine-Borel Theorem (2012)
JEFFRY L HIRST & JESSICA MILLER, JLA 2012

On page 2 of the paper,
"HB(X): X is a subset of [0,1] and for every closed (in the topology on ℝ) subset A ⊆ X, every open cover of A contains a finite sub cover"

Here we prove a scheme formalizing the Heine-Borel Theorem for subsets of [0,1] in ℝ. This will be later used to give characterization of subsets of [0,1] for which the HB theorem is equivalent to Weak Konig's Lemma (WKL0) in the big five reverse mathematics axiom systems.
-/

open Bornology

namespace HirstMiller

/-- show that an interval is bounded -/
lemma bounded_icc {r_c : ℝ} : IsBounded {r | 0 ≤ r ∧ r ≤ r_c} := by
  exact Metric.isBounded_Icc 0 r_c

/-- show that [0,1] is bounded -/
lemma subset_bounded_01 : IsBounded (Set.Icc (0:ℝ) 1) := by
  have := @bounded_icc
  apply this

/-- show that X ⊆ [0,1], is bounded -/
lemma subset_bounded_X  {X : Set ℝ} (hX : X ⊆ (Set.Icc (0:ℝ) 1)): IsBounded X := by
  have := @subset_bounded_01
  exact IsBounded.subset this hX

/-- show that A ⊆ X, is bounded -/
lemma subset_bounded_A {X} {A : Set ℝ} (hX : X ⊆ Set.Icc 0 1) (hA : A ⊆ X) : IsBounded A := by
  have := @subset_bounded_X
  exact subset_bounded_X fun ⦃a⦄ a_1 => hX (hA a_1)

/-- show that A is compact for every closed subset of A -/
theorem compact_A {A X : Set ℝ} (hX : X ⊆ (Set.Icc (0:ℝ) 1)) (hA : A ⊆ X) (hClosed: IsClosed A) : IsCompact A := by
  have hBounded : IsBounded A := by
    have := @subset_bounded_X
    apply this
    have := @subset_bounded_A
    exact fun ⦃a⦄ a_1 => hX (hA a_1)
  have := @Metric.isCompact_of_isClosed_isBounded ℝ A
  exact this hClosed hBounded

/-- show that every open cover of A contains a finite subcover -/
theorem finite_subcover_A {I} {A X : Set ℝ} (hX : X ⊆ (Set.Icc (0:ℝ) 1)) (hA : A ⊆ X) (hClosed : IsClosed A) (U : I → Set ℝ) (hOpen : ∀ i, IsOpen (U i)) (hCover : A ⊆ ⋃ i, U i) : ∃ (J : Finset I), A ⊆ ⋃ i ∈ J, U i := by
  have hCompact : IsCompact A := compact_A hX hA hClosed
  exact hCompact.elim_finite_subcover U hOpen hCover


/-!
  show that (X ⊆ [0,1], A ⊆ X) doesn't matter in HB(X)
   Thus the usual Heine-Borel theorem states "If X is closed and bounded ↔ X is compact thus every open cover of X has a finite subcover."
-/

/-- X is closed and bounded → X is compact and thus every open cover of X has a finite subcover -/
example {I} {X} (hClosed: IsClosed X) (hBounded : IsBounded X) (U : I → Set ℝ) (hOpen : ∀ i, IsOpen (U i)) (hCover : X ⊆ ⋃ i, U i) : ∃ (J : Finset I), X ⊆ ⋃ i ∈ J, U i := by
  have := @Metric.isCompact_of_isClosed_isBounded ℝ X
  exact IsCompact.elim_finite_subcover (this hClosed hBounded) U hOpen hCover

/-- X is compact → X is closed ∧ bounded -/
instance : ProperSpace ℝ := by infer_instance

example {X : Set ℝ} (hCompact : IsCompact X) : IsBounded X ∧ IsClosed X := by
  exact And.symm (Metric.isCompact_iff_isClosed_bounded.mp hCompact)

/-!
On page 2 of the paper,
"S(X): X is a subset of [0,1] and there is a countable dense in itself set Y which is contained in every closed superset of X"

Here we prove a scheme formalizing the S(X) proposition for subsets of [0,1] in ℝ. This will be later used to give characterization of subsets of [0,1] which will be used in theorem 2 to prove Weak Konig's Lemma (WKL0) and Recursive Comprehension Axiom (RCA0). Thus, theorem 2 states "If S(X) holds, then the Heine-Borel theorem for X implies WKL0. That is, S(X) implies HB(X) → WKL0." In order to do so, we prove scenarios of when S(X) holds or not.
-/

/-- show that the empty set is dense in itself (dense in itself is called preperfect in LEAN v4) -/
lemma dense_empty : Preperfect (∅ : Set ℝ) := by
  intro x hx
  simp at hx

/-- define S(X) by introducing C as the closed superset of X -/
def S
  (X : Set ℝ) : Prop := X ⊆ (Set.Icc (0:ℝ) 1) ∧ ∃ (Y : Set ℝ), Countable Y ∧ Preperfect Y ∧ ∀ C, IsClosed C ∧ X ⊆ C → Y ⊆ C

/-- define φ as "Y which is contained in every closed superset of X" -/
def φ (X Y : Set ℝ) := ∀ C, IsClosed C ∧ X ⊆ C → Y ⊆ C

/-- define ψ as S(X) except X being a subset of [0,1] is omitted -/
def ψ (X : Set ℝ) := ∃ (Y : Set ℝ), (Y ≠ ∅) ∧ Countable Y
    ∧ Preperfect Y ∧ φ X Y

/-- define S(X) in a condensed manner including [0,1] -/
def S_prime
  (X : Set ℝ) : Prop := X ⊆ (Set.Icc (0:ℝ) 1) ∧ ψ X

open Set

/-- prove S(X) is always true ∀ x ∈ [0,1] -/
lemma S_true  (X : Set ℝ) (hX : X ⊆ Icc (0 : ℝ) 1) : S X:= by
  use hX
  use ∅
  constructor
  · exact Set.countable_empty
  constructor
  · exact dense_empty
  · intro Y
    intro _hx
    exact Set.empty_subset Y

/-- prove that there is a countable dense in itself set Y which is contained in every closed superset of X -/
lemma Y_dense (Y : Set ℝ) (hY : Y ≠ ∅ ∧ Countable ↑Y ∧ Preperfect Y ∧ ∀ (C : Set ℝ), IsClosed C ∧ {1} ⊆ C → Y ⊆ C)
  (this : Y ⊆ {1}) : Y = {1} := by
  apply subset_antisymm
  exact this
  refine singleton_subset_iff.mpr ?_
  by_contra h
  have : Y = ∅ := by
    ext x
    simp only [mem_empty_iff_false, iff_false]
    intro hx
    have : x = 1 := this hx
    rw [this] at hx
    exact h hx
  exact hY.1 this

end HirstMiller
