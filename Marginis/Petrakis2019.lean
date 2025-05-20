import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic
import Mathlib.Topology.UniformSpace.Basic
import Mathlib
/-!

# Constructive uniformities of pseudometrics and Bishop topologies
[IOSIF PETRAKIS](http://logicandanalysis.org/index.php/jla/article/view/339)

discusses uniformities.
Lean's Mathlib uses uniform spaces quite a bit.
Consequently, here we use uniformities to prove that x^2 is not uniformly continuous.
-/

lemma extraabs (a : ℝ) (h : 0 < a) : 1 ≤ |1 + a| := by
  have : |1+a| = 1+a := by
    have := @abs_eq_self ℝ _ _ _ (1+a)
    rw [this]
    linarith
  rw [this]
  linarith

/-- Lemma by Clark Eggerman. -/
lemma Hδ (δ : ℝ) (hδ : 0 < δ) : 1 ≤ |δ * δ⁻¹ + δ ^ 2 * (1 / 4)| := by
  rw [CommGroupWithZero.mul_inv_cancel δ (Ne.symm (ne_of_lt hδ))]
  have h0 : 0 < δ ^ 2 * (1 / 4) := by
    simp
    exact sq_pos_of_pos hδ
  exact extraabs (δ ^ 2 * (1 / 4)) h0

/-- Example by Bjørn Kjos-Hanssen. -/
example : ¬ UniformContinuous (λ x : ℝ ↦ x^2) := by
  rw [uniformContinuous_def]
  show ¬∀ r, r ∈ uniformity ℝ → {x | (x.1 ^ 2, x.2 ^ 2) ∈ r} ∈ uniformity ℝ
  push_neg
  use {x | dist x.1 x.2 < 1}
  let Q := @Metric.mem_uniformity_dist ℝ _ {x | dist x.1 x.2 < 1}
  constructor
  rw [Q]
  simp
  use 1
  aesop

  let W := @Metric.mem_uniformity_dist ℝ _
    ({x | (x.1 ^ 2, x.2 ^ 2) ∈ {x | dist x.1 x.2 < 1}})
  rw [W]
  push_neg
  simp
  intro δ hδ
  use (1/δ)
  use (1/δ + δ/2)
  constructor
  simp
  have : |δ| = δ := by exact abs_of_pos hδ
  rw [this]
  linarith
  unfold dist PseudoMetricSpace.toDist Real.pseudoMetricSpace
  simp

  ring_nf
  have r1 : -(δ * δ⁻¹) + δ ^ 2 * (-1 / 4) = -(δ * δ⁻¹ + δ ^ 2 * (1 / 4)) := by ring_nf
  rw [r1, abs_neg (δ * δ⁻¹ + δ ^ 2 * (1 / 4))]
  exact Hδ δ hδ
#min_imports
