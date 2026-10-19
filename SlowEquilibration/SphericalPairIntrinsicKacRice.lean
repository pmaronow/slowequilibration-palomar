-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.RoundSpherePairChartIntegral
public import SlowEquilibration.SphericalPairIntrinsicCoordinates

/-! Genuine global intrinsic marked two-point Kac--Rice for the original
spherical tensor field. Every observation, Hessian, conditional law, count,
and spatial measure is the actual object; all small-overlap nondegeneracy,
metric, and chart-cover facts are proved internally. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPairIntrinsicKacRice
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open SphericalChartKacRice SphereChartVolume SphereHessian
open SphericalPairChartGeometry SphericalPairChartKacRice SphericalPairCountGluing
open SphericalPairIntrinsicCoordinates
open scoped ENNReal Topology RealInnerProductSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual ordered critical-pair counts have their literal intrinsic
Kac--Rice intensity on a proved positive overlap neighborhood, with arbitrary
nonnegative Borel marks depending on the whole original disorder. -/
theorem actual_sphere_pair_marked_kacRice (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hdeg : 4 ≤ μ.minDegree)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) × Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × (Vector (n+1) × Vector (n+1)) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let ρ := pairRadius μ hQ hdeg
    AEMeasurable (actualSpherePairCount n c ρ psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J,actualSpherePairCount n c ρ psi J ∂disorderLaw (n+1) μ.maxDegree)=
      ∫⁻ p in {p | |overlap p.1 p.2| < ρ},
        GaussianRegression.observationPdf (pairIntrinsicGamma c p.1 p.2) 0 *
          ∫⁻ J, (ENNReal.ofReal |(intrinsicHessian (field c J) p.1).det| *
            ENNReal.ofReal |(intrinsicHessian (field c J) p.2).det|) * psi J p
              ∂coefficientKernel (pairIntrinsicGamma c p.1 p.2) 0
        ∂(manuscriptRoundVolume n).prod (manuscriptRoundVolume n) := by
  have hk := actual_sphere_pair_chart_kacRice n hn μ hQ hdeg psi hpsi
  refine ⟨hk.1,hk.2.trans ?_⟩
  rw [RoundSpherePairChartIntegral.round_prod_overlap_lintegral_chart n hn]
  apply setLIntegral_congr_fun (pairOverlapDomain_isOpen n _).measurableSet
  intro p hp
  dsimp only
  rw [pair_density_metric_cancel _ hp.1 (pairOverlapDomain_surjective n μ hQ hdeg hp),
    pair_chart_coefficientKernel_zero_eq _ hp.1 (pairOverlapDomain_surjective n μ hQ hdeg hp)]
  change _ = (_ * _) * (GaussianRegression.observationPdf
    (pairIntrinsicGamma _ (manuscriptChart n p.fst) (manuscriptChart n p.snd)) 0 * _)
  ac_rfl

end SlowEquilibration.SphericalPairIntrinsicKacRice
