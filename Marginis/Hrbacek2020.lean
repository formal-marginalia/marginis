/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Janitha Aswedige
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
/-!

# On factoring of unlimited integers

[KAREL HRBACEK](http://logicandanalysis.org/index.php/jla/article/view/5)

We prove a special case of Dickson's Conjecture as stated in the paper:
the case where
* `gcd(a,b)>1` or `b=1`

n = gcd(a,b) > 1 implies n | f(k) = a+bk for all k,
violating the main hypothesis of Dickson's conjecture.

See `dickson_strong`.

Dickson's Conjecture is trivial for ℓ = 0
and we do not need Hrbacek's assumption that ℓ ≥ 1.
 -/

#eval Nat.gcd 0 5

open Finset
def prod_f {ℓ : ℕ} (a b : Fin ℓ → ℕ) (k : ℕ) : ℕ :=
  Finset.prod univ (fun i => a i + b i * k)


theorem dickson_strong {ℓ : ℕ} (a b: Fin ℓ → ℕ)
  (ha : ∀ i, Nat.gcd (a i) (b i) > 1 ∨ b i = 1)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime := by
  by_cases h : ∀ i, b i = 1
  . rw [h i]
    simp
    let Q := Nat.exists_infinite_primes (a i + n₀)
    obtain ⟨p,hp⟩ := Q
    exists (p - a i)
    constructor
    . suffices a i + n₀ ≤ a i + (p - a i) by
        refine Nat.le_sub_of_add_le ?h
        linarith

      calc
      a i + n₀ ≤ p := hp.1
      _ ≤ _ := le_add_tsub
    have : a i + (p - a i) = p := by
      apply Nat.add_sub_of_le
      linarith
    rw [this]
    exact hp.2
  . simp at h
    obtain ⟨i,_⟩ := h
    exfalso
    revert hc
    simp
    exists Nat.gcd (a i) (b i)
    constructor
    . have := ha i
      tauto
    . intro k
      let h₀ := prod_dvd_prod_of_subset {i} univ
        (fun j : Fin ℓ => a j + b j * k) (subset_univ {i})
      rw [prod_singleton] at h₀
      unfold prod_f
      have h₁ : b i ∣ b i * k := Nat.dvd_mul_right (b i) k
      have h₂: (a i).gcd (b i) ∣ a i := Nat.gcd_dvd_left (a i) (b i)
      have h₃: (a i).gcd (b i) ∣ b i := Nat.gcd_dvd_right (a i) (b i)
      have h₄: (a i).gcd (b i) ∣ a i + b i * k := by
        refine (Nat.dvd_add_iff_right h₂).mp ?_
        exact Nat.dvd_trans h₃ h₁
      exact Nat.dvd_trans h₄ h₀

theorem dickson_gcd {ℓ : ℕ} (a b: Fin ℓ → ℕ)
  (ha : ∀ i, Nat.gcd (a i) (b i) > 1)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime :=
  dickson_strong a b (by tauto) hc i n₀

lemma dvd_helper' {a b : ℕ} (ha : b ∣ a) (h_b : b > 1):
  Nat.gcd a b > 1 := by
    have hb : b ≥ 1 := by exact Nat.one_le_of_lt h_b
    unfold Nat.gcd
    by_cases Ha : a = 0
    . rw [if_pos Ha]
      tauto
    rw [if_neg Ha]
    obtain ⟨k,hk⟩ := ha
    have hobby: b ∣ b.gcd (b * k) := by
      refine Nat.dvd_gcd_iff.mpr ?_
      constructor
      . simp
      . exact Nat.dvd_mul_right b k
    rw [hk]
    simp
    by_cases Hab : a = b
    . rw [Hab] at hk
      have : k = 1 := (Nat.mul_right_eq_self_iff hb).mp (id (Eq.symm hk))
      subst this;simp;tauto
    . have hk₀: k ≠ 0 := by intro hc;subst hc;simp at hk;tauto
      have hk₁: k ≠ 1 := by intro hc;subst hc;simp at hk;tauto
      have hk1: k > 1 := by omega
      have : b % (b * k) = b := Nat.mod_eq_of_lt <| (Nat.lt_mul_iff_one_lt_right (hb)).mpr hk1
      rw [this]
      have g₀ : (b).gcd (b * k) ≠ 0 := by
        refine Nat.gcd_ne_zero_left ?_
        intro hc
        rw [hc] at hb
        tauto
      have g₁ : b.gcd (b * k) ≠ 1 := by
        intro hc
        have : b ∣ 1 :=
          (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hc) (b.gcd (b * k))) hobby).mp hobby
        simp at this
        linarith
      omega


lemma dvd_helper {a b : ℕ} (ha : b ∣ a) (hb : b ≥ 1):
  Nat.gcd a b > 1 ∨ b = 1 := by
    by_cases H : b = 1
    tauto
    left
    have hbi: b > 1 := Nat.lt_of_le_of_ne (hb) fun a => H (id (Eq.symm a))
    exact dvd_helper' ha hbi


lemma dickson_dvd {ℓ : ℕ} (a b: Fin ℓ → ℕ) (hb : ∀ i, b i ≥ 1)
  (ha : ∀ i, b i ∣ a i)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime :=
  dickson_strong a b (fun i => dvd_helper (ha i) (hb i)) hc i n₀

  -- We could also prove dickson_dvd without using dickson_strong and dvd_helper:
  -- by
  -- by_cases h : ∀ i, b i = 1
  -- . rw [h i]
  --   simp
  --   let Q := Nat.exists_infinite_primes (a i + n₀)
  --   obtain ⟨p,hp⟩ := Q
  --   exists (p - a i)
  --   constructor
  --   . suffices a i + n₀ ≤ a i + (p - a i) by
  --       refine Nat.le_sub_of_add_le ?h
  --       linarith

  --     calc
  --     a i + n₀ ≤ p := hp.1
  --     _ ≤ _ := le_add_tsub
  --   have : a i + (p - a i) = p := by
  --     apply Nat.add_sub_of_le
  --     linarith
  --   rw [this]
  --   exact hp.2
  -- . simp at h;obtain ⟨i,hi⟩ := h;exfalso;contrapose hc;simp;exists b i
  --   constructor
  --   . exact Nat.lt_of_le_of_ne (hb i) fun a => hi (id (Eq.symm a))
  --   . intro k
  --     let h₀ := prod_dvd_prod_of_subset {i} univ
  --       (fun j : Fin ℓ => a j + b j * k) (subset_univ {i})
  --     rw [prod_singleton] at h₀
  --     unfold prod_f
  --     have h₁ : b i ∣ b i * k := Nat.dvd_mul_right (b i) k
  --     have h₂ : b i ∣ a i + b i * k := (Nat.dvd_add_iff_right (ha i)).mp h₁
  --     simp at h₀
  --     exact Nat.dvd_trans h₂ h₀


  theorem dickson_linear {ℓ : ℕ} {a b: Fin ℓ → ℕ} {hb : ∀ i, b i ≥ 1}
  (ha : ∀ i, a i = 0)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime := by
    rw [ha i]
    simp
    let Q := dickson_dvd a b hb (by
      intro i;
      rw [ha i];
      exact Nat.dvd_zero (b i)
    ) hc i n₀
    rw [ha i] at Q
    simp at Q
    exact Q

/-!

# Janitha Aswedige's part
-/

lemma Div_by_3 (m : ℕ) : 3 ∣ (1 - (-2)^m) := by
  induction' m with m ih
  ring_nf
  omega
  rw [pow_succ]
  have D11 : 1 - (-2) ^ m * -2 = 1 - (-2)^m + 3 * (-2)^m := by ring
  obtain ⟨k, hk⟩ := ih
  rw [hk] at D11
  rw [D11]
  omega

lemma help (m : ℕ) : 2 ^ m / (-2) ^ m = (-1)^m := by
  induction m with
  |zero =>
  simp
  |succ m ih =>
  rw [pow_succ, pow_succ, pow_succ]
  field_simp
  exact ih

--Definition 2.
--The anchor function for a prime p and a natural number n is defined.

/-- Anchor function definition.
For p > 2: s(p, n) = (p^n + 1)/2
For p = 2: s(p, n) = (1 - (-2)^n)/3 -/
def s : ℕ → ℕ → ℤ
  | p, n =>
    if p > 2 then
      (p^n + 1) / 2
    else if p = 2 then
      (1 - (-2)^n) / 3
    else
      0

--Lemma 3.
lemma anchor (p m n : ℕ) (hp : Nat.Prime p) (hmn : m < n) : s p n ≡ s p m [ZMOD p^m] := by
  have : p = 2 ∨ p > 2 := by
    refine LE.le.eq_or_gt ?_
    exact Nat.Prime.two_le hp
  rcases this with H|H
  simp only [s]
  split_ifs with h1
  exfalso
  linarith
  rw [H]
  refine Int.modEq_iff_dvd.mpr ?_
  zify
  have D1 : 3 ∣ (1 - (-2)^m) := by
    apply Div_by_3
  have D2 : 3 ∣ (1 - (-2)^n) := by
    apply Div_by_3
  have H1 : (1 - (-2) ^ m) / 3 - (1 - (-2) ^ n) / 3 = ((-2)^n - (-2)^m) / 3 := by omega
  have H2 : ((-2)^n - (-2)^m) / 3 = (-2)^m * (((-2)^(n - m) - 1) / 3) := by
    have : (-2) ^ m * (((-2) ^ (n - m) - 1) / 3) = ((-2) ^ m * (((-2) ^ (n - m) - 1))) / 3 := by
      refine Eq.symm (Int.mul_ediv_assoc ((-2) ^ m) ?_)
      have : 3 ∣ 1 - (-2) ^ (n - m) := by
        apply Div_by_3
      omega
    rw [this]
    rw [mul_sub]
    rw [←pow_add]
    have : m + (n - m) = n := by omega
    rw [this]
    rw [mul_one]
  rw [H1, H2]
  refine Int.dvd_mul_of_div_dvd ?_ ?_
  refine pow_dvd_pow_of_dvd ?_ m
  norm_num
  have H3 : 2 ^ m / (-2) ^ m = (-1)^m := by apply help
  rw [H3]
  have H4 : 3 ∣ ((-2) ^ (n - m) - 1) := by
    have : 3 ∣ (1 - (-2)^(n - m)) := by
      apply Div_by_3
    omega
  obtain ⟨k, hk⟩ := H4
  rw [hk]
  have : (3 * k) / 3 = k := by omega
  rw [this]
  have H5 : (-1)^m = -1 ∨ (-1)^m = 1 := by
    have cases : Even m ∨ Odd m := by exact Nat.even_or_odd m
    rcases cases with L|L
    right
    exact Even.neg_one_pow L
    left
    exact Odd.neg_one_pow L
  rcases H5 with J|J
  rw [J]
  refine Int.neg_dvd.mpr ?_
  omega
  rw [J]
  omega
  simp only [s]
  split_ifs
  refine Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) ?_)
  have h1 : ((p : ℤ) ^ n + 1) / 2 - ((p : ℤ) ^ m + 1) / 2 = ((p : ℤ) ^ n - (p : ℤ) ^ m) / 2 := by
    have h11 : 2 ∣ ((p : ℤ) ^ n + 1) := by
      have : Even (((p : ℤ) ^ n + 1)) := by
        refine Odd.add_one ?_
        refine Odd.pow ?_
        norm_cast
        by_contra h
        have : Even p := by exact Nat.not_odd_iff_even.mp h
        have : p = 2 := by exact (Nat.Prime.even_iff hp).mp this
        omega
      exact even_iff_two_dvd.mp this
    have h12 : 2 ∣ ((p : ℤ) ^ m + 1) := by
      have : Even (((p : ℤ) ^ m + 1)) := by
        refine Odd.add_one ?_
        refine Odd.pow ?_
        norm_cast
        by_contra h
        have : Even p := by exact Nat.not_odd_iff_even.mp h
        have : p = 2 := by exact (Nat.Prime.even_iff hp).mp this
        omega
      exact even_iff_two_dvd.mp this
    omega
  rw [h1]
  have h2 : p^n = p^m * p^(n - m) := by
    refine Eq.symm (pow_mul_pow_sub ↑p ?_)
    linarith
  zify at h2
  rw [h2]
  use (p^(n - m) - 1) / 2
  rw [← pow_add, ← Nat.add_sub_of_le hmn]
  have h11 : m + (m.succ + (n - m.succ) - m) = n := by omega
  have h22 : m.succ + (n - m.succ) - m = n - m := by omega
  rw [h11, h22]
  have h33 : (p : ℤ) ^ m * (((p : ℤ) ^ (n - m) - 1) / 2) =  ((p : ℤ) ^ m * ((p : ℤ) ^ (n - m) - 1)) / 2 := by
    refine Eq.symm (Int.mul_ediv_assoc (↑p ^ m) ?_)
    have h331 : Odd (p^(n - m)) := by
      refine Odd.pow ?_
      by_contra h
      have : Even p := by exact Nat.not_odd_iff_even.mp h
      have : p = 2 := by exact (Nat.Prime.even_iff hp).mp this
      omega
    obtain ⟨l, hl⟩ := h331
    zify at *
    rw [hl]
    omega
  rw [h33]
  rw [mul_sub]
  rw [← pow_add]
  have : m + (n - m) = n := by omega
  rw [this]
  rw [mul_one]
