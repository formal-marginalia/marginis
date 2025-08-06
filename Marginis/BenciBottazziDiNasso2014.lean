import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Hyperreal
/-!

## Elementary numerosity and measures

[VIERI BENCI, EMANUELE BOTTAZZI, and MAURO DI NASSO](http://logicandanalysis.org/index.php/jla/article/view/212)

We construct a cardinality map from the powerset of any Fintype to the hyperreals.
-/

/-- Cardinality of a finite set, as a hyperreal. -/
noncomputable def size {B : Type} [Fintype B] : Finset B → Hyperreal := by
  intro S
  let c := S.card
  apply Hyperreal.ofReal
  exact (c : ℝ)

/-- The cardinality of the empty set, as a hyperreal. -/
lemma size_empty {B : Type} [Fintype B] : size (B := B) ∅ = 0 := by
  unfold size
  simp only [Finset.card_empty, CharP.cast_eq_zero, Hyperreal.coe_zero]

/-- The cardinality of Bool, as a hyperreal. -/
lemma size_univ : size (Finset.univ : Finset Bool) = 2 := by
  unfold size
  simp

/-- The cardinality of a singleton, as a hyperreal. -/
lemma size_single {B : Type} [Fintype B] (b : B) : size {b} = 1 := by
  unfold size
  simp only [Finset.card_singleton, Nat.cast_one, Hyperreal.coe_one]
