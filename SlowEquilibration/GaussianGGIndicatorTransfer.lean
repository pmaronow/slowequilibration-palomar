-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGPolynomialTests
public import Mathlib.Probability.HasLaw

/-! Ordinary-measure GG discrepancies and negative-indicator transfer.
The overlap marginals are genuine `HasLaw` statements. The discrepancy
is constructed from the actual replica expectations; its norm bound is
proved from probability and boundedness, not supplied as an operator
assumption. Continuous cutoffs approximate their negative steps through
actual pair-law shell mass. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGIndicatorTransfer

open MeasureTheory ProbabilityTheory Set
open GaussianGGCutoffs GaussianGGPolynomialTests
open scoped Topology BigOperators

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The literal normalized GG discrepancy with m old neighbors and one
fresh neighbor, hence m+1 replicas in the original bounded observable. -/
def discrepancy (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ) (ψ : ℝ → ℝ) : ℝ :=
  (∫ ω, f ω * ψ (R ω) ∂μ) -
    (∫ ω, f ω ∂μ) * (∫ r, ψ r ∂ρ) / ((m:ℝ)+1) -
    (∑ j : Fin m, ∫ ω, f ω * ψ (Q j ω) ∂μ) / ((m:ℝ)+1)

private theorem weighted_integrable (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1) (hR : HasLaw R ρ μ)
    {ψ : ℝ → ℝ} (hψ : Integrable ψ ρ) :
    Integrable (fun ω => f ω * ψ (R ω)) μ := by
  apply (hR.integrable_comp hψ).bdd_mul hf
  exact hb.mono fun ω h => by simpa only [Real.norm_eq_abs] using h

/-- A bounded replica observable cannot increase the L¹ norm of its
actual overlap test. The asserted marginal law is used to change variables. -/
theorem weighted_expectation_abs_le (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1) (hR : HasLaw R ρ μ)
    {ψ : ℝ → ℝ} (hψ : Integrable ψ ρ) :
    |∫ ω, f ω * ψ (R ω) ∂μ| ≤ ∫ r, |ψ r| ∂ρ := by
  have hi := weighted_integrable μ ρ f R hf hb hR hψ
  have hi' := hR.integrable_comp hψ.abs
  calc
    _ ≤ ∫ ω, |f ω * ψ (R ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |ψ (R ω)| ∂μ := integral_mono_ae hi.abs hi' (hb.mono fun ω h => by
      change |f ω * ψ (R ω)| ≤ |ψ (R ω)|
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h (abs_nonneg (ψ (R ω))))
    _ = _ := hR.integral_comp hψ.abs.aestronglyMeasurable

/-- The normalized discrepancy has exact L¹ operator bound two. -/
theorem discrepancy_abs_le_l1 (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀ j, HasLaw (Q j) ρ μ)
    {ψ : ℝ → ℝ} (hψ : Integrable ψ ρ) :
    |discrepancy m μ ρ f R Q ψ| ≤ 2 * (∫ r, |ψ r| ∂ρ) := by
  let L := ∫ r, |ψ r| ∂ρ
  have hL : 0 ≤ L := integral_nonneg fun _ => abs_nonneg _
  have hF : |∫ ω, f ω ∂μ| ≤ 1 := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1) (hb.mono fun ω h => by simpa only [Real.norm_eq_abs] using h)
  have hP : |∫ r, ψ r ∂ρ| ≤ L := abs_integral_le_integral_abs
  have hFresh : |∫ ω, f ω*ψ (R ω) ∂μ| ≤ L :=
    weighted_expectation_abs_le μ ρ f R hf hb hR hψ
  have hOld : |∑ j : Fin m, ∫ ω, f ω*ψ (Q j ω) ∂μ| ≤ (m:ℝ)*L := by
    calc
      _ ≤ ∑ j : Fin m, |∫ ω, f ω*ψ (Q j ω) ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin m, L := Finset.sum_le_sum fun j _ =>
        weighted_expectation_abs_le μ ρ f (Q j) hf hb (hQ j) hψ
      _ = _ := by simp
  have hMiddle : |(∫ ω, f ω ∂μ)*(∫ r, ψ r ∂ρ)| ≤ L := by
    rw [abs_mul]
    calc
      _ ≤ 1*L := mul_le_mul hF hP (abs_nonneg _) (by norm_num)
      _ = L := one_mul L
  have hn : 0 < (m:ℝ)+1 := by positivity
  have htri' : |discrepancy m μ ρ f R Q ψ| ≤
      |∫ ω,f ω*ψ (R ω) ∂μ| +
      |(∫ ω,f ω ∂μ)*(∫ r,ψ r ∂ρ)|/((m:ℝ)+1) +
      |∑ j : Fin m, ∫ ω,f ω*ψ (Q j ω) ∂μ|/((m:ℝ)+1) := by
    unfold discrepancy
    calc
      _ ≤ |(∫ ω,f ω*ψ (R ω) ∂μ)-
          (∫ ω,f ω ∂μ)*(∫ r,ψ r ∂ρ)/((m:ℝ)+1)| +
          |(∑ j : Fin m, ∫ ω,f ω*ψ (Q j ω) ∂μ)/((m:ℝ)+1)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_div,abs_of_pos hn]
        have ht := abs_sub (∫ ω,f ω*ψ (R ω) ∂μ)
          ((∫ ω,f ω ∂μ)*(∫ r,ψ r ∂ρ)/((m:ℝ)+1))
        rw [abs_div,abs_of_pos hn] at ht
        linarith
  calc
    _ ≤ |∫ ω,f ω*ψ (R ω) ∂μ| +
      |(∫ ω,f ω ∂μ)*(∫ r,ψ r ∂ρ)|/((m:ℝ)+1) +
      |∑ j : Fin m, ∫ ω,f ω*ψ (Q j ω) ∂μ|/((m:ℝ)+1) := htri'
    _ ≤ L+L/((m:ℝ)+1)+((m:ℝ)*L)/((m:ℝ)+1) := by
      exact add_le_add (add_le_add hFresh (div_le_div_of_nonneg_right hMiddle hn.le))
        (div_le_div_of_nonneg_right hOld hn.le)
    _ = 2*L := by field_simp; ring

/-- Linearity is proved on actual integrable tests, before forming a
continuous linear functional. -/
theorem discrepancy_sub (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀ j, HasLaw (Q j) ρ μ)
    {ψ χ : ℝ → ℝ} (hψ : Integrable ψ ρ) (hχ : Integrable χ ρ) :
    discrepancy m μ ρ f R Q (fun r => ψ r-χ r) =
      discrepancy m μ ρ f R Q ψ-discrepancy m μ ρ f R Q χ := by
  have hF : (∫ ω,f ω*(ψ (R ω)-χ (R ω)) ∂μ)=
      (∫ ω,f ω*ψ (R ω) ∂μ)-(∫ ω,f ω*χ (R ω) ∂μ) := by
    simp_rw [mul_sub]
    exact integral_sub (weighted_integrable μ ρ f R hf hb hR hψ)
      (weighted_integrable μ ρ f R hf hb hR hχ)
  have hOld (j : Fin m) : (∫ ω,f ω*(ψ (Q j ω)-χ (Q j ω)) ∂μ)=
      (∫ ω,f ω*ψ (Q j ω) ∂μ)-(∫ ω,f ω*χ (Q j ω) ∂μ) := by
    simp_rw [mul_sub]
    exact integral_sub (weighted_integrable μ ρ f (Q j) hf hb (hQ j) hψ)
      (weighted_integrable μ ρ f (Q j) hf hb (hQ j) hχ)
  unfold discrepancy
  rw [hF,integral_sub hψ hχ]
  simp_rw [hOld]
  rw [Finset.sum_sub_distrib]
  ring

theorem discrepancy_add (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀ j, HasLaw (Q j) ρ μ)
    {ψ χ : ℝ → ℝ} (hψ : Integrable ψ ρ) (hχ : Integrable χ ρ) :
    discrepancy m μ ρ f R Q (fun r => ψ r+χ r) =
      discrepancy m μ ρ f R Q ψ+discrepancy m μ ρ f R Q χ := by
  have hF : (∫ ω,f ω*(ψ (R ω)+χ (R ω)) ∂μ)=
      (∫ ω,f ω*ψ (R ω) ∂μ)+(∫ ω,f ω*χ (R ω) ∂μ) := by
    simp_rw [mul_add]
    exact integral_add (weighted_integrable μ ρ f R hf hb hR hψ)
      (weighted_integrable μ ρ f R hf hb hR hχ)
  have hOld (j : Fin m) : (∫ ω,f ω*(ψ (Q j ω)+χ (Q j ω)) ∂μ)=
      (∫ ω,f ω*ψ (Q j ω) ∂μ)+(∫ ω,f ω*χ (Q j ω) ∂μ) := by
    simp_rw [mul_add]
    exact integral_add (weighted_integrable μ ρ f (Q j) hf hb (hQ j) hψ)
      (weighted_integrable μ ρ f (Q j) hf hb (hQ j) hχ)
  unfold discrepancy
  rw [hF,integral_add hψ hχ]
  simp_rw [hOld]
  rw [Finset.sum_add_distrib]
  ring

theorem discrepancy_smul (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ) (ψ : ℝ → ℝ) (c : ℝ) :
    discrepancy m μ ρ f R Q (fun r => c*ψ r) =
      c*discrepancy m μ ρ f R Q ψ := by
  have hF : (∫ ω,f ω*(c*ψ (R ω)) ∂μ)=c*(∫ ω,f ω*ψ (R ω) ∂μ) := by
    simp_rw [show ∀ω, f ω*(c*ψ (R ω))=c*(f ω*ψ (R ω)) from fun ω => by ring]
    exact integral_const_mul _ _
  have hOld (j : Fin m) : (∫ ω,f ω*(c*ψ (Q j ω)) ∂μ)=
      c*(∫ ω,f ω*ψ (Q j ω) ∂μ) := by
    simp_rw [show ∀ω, f ω*(c*ψ (Q j ω))=c*(f ω*ψ (Q j ω)) from fun ω => by ring]
    exact integral_const_mul _ _
  unfold discrepancy
  rw [hF,integral_const_mul]
  simp_rw [hOld]
  rw [← Finset.mul_sum]
  ring

/-- An overlap-supported law permits restriction to the true interval
without changing any replica expectation. -/
theorem discrepancy_congr_on_interval (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ)
    (hρ : ∀ᵐ r ∂ρ, r∈Icc (-1:ℝ) 1)
    {ψ χ : ℝ → ℝ} (heq : ∀r∈Icc (-1:ℝ) 1, ψ r=χ r) :
    discrepancy m μ ρ f R Q ψ=discrepancy m μ ρ f R Q χ := by
  have hFresh : ∀ᵐ ω ∂μ, R ω∈Icc (-1:ℝ) 1 :=
    (hR.ae_iff (measurableSet_setOfPred.mp measurableSet_Icc)).mpr hρ
  have hOld (j : Fin m) : ∀ᵐ ω ∂μ, Q j ω∈Icc (-1:ℝ) 1 :=
    ((hQ j).ae_iff (measurableSet_setOfPred.mp measurableSet_Icc)).mpr hρ
  have hF : (∫ω,f ω*ψ (R ω) ∂μ)=(∫ω,f ω*χ (R ω) ∂μ) :=
    integral_congr_ae (hFresh.mono fun ω h => congrArg (fun z => f ω*z) (heq _ h))
  have hQ' (j : Fin m) : (∫ω,f ω*ψ (Q j ω) ∂μ)=(∫ω,f ω*χ (Q j ω) ∂μ) :=
    integral_congr_ae ((hOld j).mono fun ω h => congrArg (fun z => f ω*z) (heq _ h))
  unfold discrepancy
  rw [hF,integral_congr_ae (hρ.mono fun r h => heq r h)]
  simp_rw [hQ']

/-- The constant test has identically zero discrepancy. -/
theorem discrepancy_one (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ) :
    discrepancy m μ ρ f R Q (fun _ => 1)=0 := by
  unfold discrepancy
  simp only [mul_one,integral_const,probReal_univ,smul_eq_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (m:ℝ)+1≠0 := by positivity
  field_simp
  ring

/-- Ordinary L¹ transfer, including discontinuous indicators; no
indicator GG identity is assumed. -/
theorem discrepancy_l1_lipschitz (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀ j, HasLaw (Q j) ρ μ)
    {ψ χ : ℝ → ℝ} (hψ : Integrable ψ ρ) (hχ : Integrable χ ρ) :
    |discrepancy m μ ρ f R Q ψ-discrepancy m μ ρ f R Q χ| ≤
      2*(∫ r, |ψ r-χ r| ∂ρ) := by
  rw [← discrepancy_sub m μ ρ f R Q hf hb hR hQ hψ hχ]
  exact discrepancy_abs_le_l1 m μ ρ f R Q hf hb hR hQ (hψ.sub hχ)

/-- Genuine cutoff-to-negative-step transfer through actual shell mass. -/
theorem discrepancy_cutoff_indicator_le (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀ j, HasLaw (Q j) ρ μ)
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) (j : Fin M) :
    |discrepancy m μ ρ f R Q (cutoff ε M j)-
      discrepancy m μ ρ f R Q ((Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ)))| ≤
      2*ρ.real (shell ε M j) := by
  have hψ : Integrable (cutoff ε M j) ρ := by
    apply Integrable.of_bound (cutoff_contDiff ε M j).continuous.measurable.aestronglyMeasurable 1
    exact .of_forall fun r => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_mem ε M j r).1]
      exact (cutoff_mem ε M j r).2
  have hχ : Integrable ((Iic (leftEndpoint ε M j)).indicator (fun _ : ℝ => (1:ℝ))) ρ :=
    (integrable_const (μ := ρ) (1:ℝ)).indicator measurableSet_Iic
  exact (discrepancy_l1_lipschitz m μ ρ f R Q hf hb hR hQ hψ hχ).trans
    (mul_le_mul_of_nonneg_left (cutoff_indicator_L1_le_shell_mass ρ hε hM j) (by norm_num))

end SlowEquilibration.GaussianGGIndicatorTransfer
