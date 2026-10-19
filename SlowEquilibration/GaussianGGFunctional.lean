-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGIndicatorTransfer
public import Mathlib.Topology.Order.ProjIcc

/-! The GG continuous linear functional constructed from literal ordinary
probability expectations. Projection onto [-1,1] is only a total-function
extension of a continuous test; all applications to true overlaps are
proved equal to the original tests through their actual supported law. -/

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

/-- Continuous extension of a test, agreeing with it on the actual
physical overlap interval. -/
def extendTest (ψ : Tests) (r : ℝ) : ℝ := ψ (projIcc (-1:ℝ) 1 (by norm_num) r)

theorem extendTest_continuous (ψ : Tests) : Continuous (extendTest ψ) :=
  ψ.continuous.comp continuous_projIcc

theorem extendTest_norm_le (ψ : Tests) (r : ℝ) : ‖extendTest ψ r‖ ≤ ‖ψ‖ :=
  ψ.norm_coe_le_norm _

theorem extendTest_integrable (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (ψ : Tests) :
    Integrable (extendTest ψ) ρ :=
  Integrable.of_bound (extendTest_continuous ψ).measurable.aestronglyMeasurable ‖ψ‖
    (.of_forall (extendTest_norm_le ψ))

theorem extendTest_eq_of_mem (ψ : Tests) {r : ℝ} (hr : r∈Icc (-1:ℝ) 1) :
    extendTest ψ r=ψ ⟨r,hr⟩ := by
  unfold extendTest
  rw [projIcc_of_mem _ hr]

def discrepancyLinearMap (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) : Tests →ₗ[ℝ] ℝ where
  toFun ψ := discrepancy m μ ρ f R Q (extendTest ψ)
  map_add' ψ χ := by
    change discrepancy m μ ρ f R Q (fun r => extendTest ψ r+extendTest χ r)=_
    exact discrepancy_add m μ ρ f R Q hf hb hR hQ
      (extendTest_integrable ρ ψ) (extendTest_integrable ρ χ)
  map_smul' c ψ := by
    change discrepancy m μ ρ f R Q (fun r => c*extendTest ψ r)=
      c*discrepancy m μ ρ f R Q (extendTest ψ)
    exact discrepancy_smul m μ ρ f R Q (extendTest ψ) c

theorem discrepancyLinearMap_bound (m : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) (ψ : Tests) :
    ‖discrepancyLinearMap m μ ρ f R Q hf hb hR hQ ψ‖ ≤ 2*‖ψ‖ := by
  have hL : (∫r, |extendTest ψ r| ∂ρ) ≤ ‖ψ‖ := by
    have h := integral_mono_ae (extendTest_integrable ρ ψ).abs (integrable_const ‖ψ‖)
      (.of_forall fun r => by simpa only [Real.norm_eq_abs] using extendTest_norm_le ψ r)
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h
  change |discrepancy m μ ρ f R Q (extendTest ψ)| ≤ 2*‖ψ‖
  exact (discrepancy_abs_le_l1 m μ ρ f R Q hf hb hR hQ
    (extendTest_integrable ρ ψ)).trans (mul_le_mul_of_nonneg_left hL (by norm_num))

/-- The genuine GG functional built from the actual probability law and
its actual old/fresh overlap marginals. -/
def functional (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) : Tests →L[ℝ] ℝ :=
  (discrepancyLinearMap m μ ρ f R Q hf hb hR hQ).mkContinuous 2
    (discrepancyLinearMap_bound m μ ρ f R Q hf hb hR hQ)

theorem functional_apply (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) (ψ : Tests) :
    functional m μ ρ f R Q hf hb hR hQ ψ=discrepancy m μ ρ f R Q (extendTest ψ) := rfl

theorem functional_norm_le (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) :
    ‖functional m μ ρ f R Q hf hb hR hQ‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- The true overlap support removes the total-function extension from
any measurable test agreeing with the continuous interval test. -/
theorem functional_apply_of_agree (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ)
    (hρ : ∀ᵐ r ∂ρ, r∈Icc (-1:ℝ) 1) (ψ : Tests) (χ : ℝ → ℝ)
    (heq : ∀r (hr : r∈Icc (-1:ℝ) 1), ψ ⟨r,hr⟩=χ r) :
    functional m μ ρ f R Q hf hb hR hQ ψ=discrepancy m μ ρ f R Q χ := by
  rw [functional_apply]
  apply discrepancy_congr_on_interval m μ ρ f R Q hR hQ hρ
  intro r hr
  rw [extendTest_eq_of_mem ψ hr]
  exact heq r hr

theorem functional_apply_power (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ)
    (hρ : ∀ᵐ r ∂ρ, r∈Icc (-1:ℝ) 1) (k : ℕ) :
    functional m μ ρ f R Q hf hb hR hQ (powerTest k)=
      discrepancy m μ ρ f R Q (fun r => r^k) :=
  functional_apply_of_agree m μ ρ f R Q hf hb hR hQ hρ _ _ (fun _ _ => rfl)

theorem functional_apply_cutoff (m : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ)
    (hρ : ∀ᵐ r ∂ρ, r∈Icc (-1:ℝ) 1) (ε : ℝ) (M : ℕ) (j : Fin M) :
    functional m μ ρ f R Q hf hb hR hQ (cutoffTest ε M j)=
      discrepancy m μ ρ f R Q (cutoff ε M j) :=
  functional_apply_of_agree m μ ρ f R Q hf hb hR hQ hρ _ _ (fun _ _ => rfl)

/-- Finite power GG defects bound the actual negative-step GG defect.
Every term is an original ordinary probability expectation. -/
theorem indicator_discrepancy_le_power_defects (m : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ)
    (hρ : ∀ᵐ r ∂ρ, r∈Icc (-1:ℝ) 1)
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) (j : Fin M)
    (P : Polynomial ℝ) {K : ℕ} (hK : P.natDegree ≤ K)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀r∈Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r| ≤ δ)
    (d : ℕ → ℝ)
    (hpower : ∀k∈Finset.range (K+1), |discrepancy m μ ρ f R Q (fun r => r^k)| ≤ d k) :
    |discrepancy m μ ρ f R Q ((Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ)))| ≤
      (∑k∈Finset.range (K+1), |P.coeff k| * d k)+2*δ+2*ρ.real (shell ε M j) := by
  let D := functional m μ ρ f R Q hf hb hR hQ
  have hp : ∀k∈Finset.range (K+1), |D (powerTest k)| ≤ d k := by
    intro k hk
    rw [show D (powerTest k)=discrepancy m μ ρ f R Q (fun r => r^k) from
      functional_apply_power m μ ρ f R Q hf hb hR hQ hρ k]
    exact hpower k hk
  have hc := cutoff_discrepancy_le D (functional_norm_le m μ ρ f R Q hf hb hR hQ)
    ε M j P hK hδ happrox d hp
  rw [show D (cutoffTest ε M j)=discrepancy m μ ρ f R Q (cutoff ε M j) from
    functional_apply_cutoff m μ ρ f R Q hf hb hR hQ hρ ε M j] at hc
  have hi := discrepancy_cutoff_indicator_le m μ ρ f R Q hf hb hR hQ hε hM j
  have ht := abs_sub_le (discrepancy m μ ρ f R Q
    ((Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ))))
    (discrepancy m μ ρ f R Q (cutoff ε M j)) 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm] at hi
  linarith

end SlowEquilibration.GaussianGGIndicatorTransfer
