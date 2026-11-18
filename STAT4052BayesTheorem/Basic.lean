

/-
Copyright (c) 2026 STAT 4052 Project Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: STAT 4052 Project Team
-/


import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Basic.ENNReal.Basic

/-!
# STAT 4052 Bayes' Theorem Project

Formal verification of Bayes' Theorem using Lean 4.
-/

theorem bayes_theorem
    (pA pB pAgivenB pBgivenA : ℝ)
    (hB : pB > 0)
    (h1 : pAgivenB * pB = pBgivenA * pA) :
    pAgivenB = (pBgivenA * pA) / pB := by
  have hB_ne : pB ≠ 0 := ne_of_gt hB
  apply (eq_div_iff hB_ne).2
  exact h1

theorem probability_identity
    (pB pAB : ℝ)
    (hB : pB > 0) :
    (pAB / pB) * pB = pAB := by
  have hB_ne : pB ≠ 0 := ne_of_gt hB
  field_simp

theorem intersection_commutes
    {Ω : Type*}
    (A B : Set Ω) :
    A ∩ B = B ∩ A := by
  ext x
  simp [and_comm]

theorem probability_intersection_commutes
    {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (A B : Set Ω) :
    μ (A ∩ B) = μ (B ∩ A) := by
  rw [Set.inter_comm]

noncomputable def conditionalProb
    {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (A B : Set Ω) : ENNReal :=
  μ (A ∩ B) / μ B

theorem bayes_probability
    {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (A B : Set Ω)
    (hA : μ A ≠ 0)
    (hA_top : μ A ≠ ⊤) :
    conditionalProb μ A B =
      (conditionalProb μ B A * μ A) / μ B := by
  unfold conditionalProb
  rw [Set.inter_comm B A]
  rw [ENNReal.div_mul_cancel hA hA_top]

theorem bayes_probability_standard
    {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Set Ω)
    (hA : μ A ≠ 0)
    (_hB : μ B ≠ 0) :
    conditionalProb μ A B =
      (conditionalProb μ B A * μ A) / μ B := by
  have hA_top : μ A ≠ ⊤ := by
    have h : μ A ≤ 1 := by
      calc
        μ A ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ A)
        _ = 1 := MeasureTheory.measure_univ
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  exact bayes_probability μ A B hA hA_top
