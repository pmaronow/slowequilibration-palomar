-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorGrouping

/-! Pointwise identification of the physical Kac--Rice pair densities
with the ordinary physical four-mark and proper two-height densities. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw PairObservationTargets
open SphericalPairMarkedWindows
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma scorePairTarget_physical_smul (N:ℕ) (h1 k1 h2 k2:ℝ) :
    scorePairTarget N h1 k1 h2 k2=Real.sqrt (N:ℝ) •
      (WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2]):ScorePairSpace):=by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> apply WithLp.ofLp_injective <;> funext i <;> fin_cases i <;> rfl

lemma valueScorePairTarget_physical_smul (N:ℕ) (h1 h2:ℝ) :
    valueScorePairTarget N h1 h2=Real.sqrt (N:ℝ) • (WithLp.toLp 2 (h1,h2):ValuePairSpace):=by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> rfl

theorem source_pair_mixed_physical_pdf_eq {n P:ℕ} (c:Degree P→ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 k1 h2 k2:ℝ) :
    pairMixedPhysicalPdf c x y hx hy
      (WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2]))=
      ENNReal.ofReal (physicalPairScoreDensity (n+3)
        (residualPairScore c x y (tangentFrame x hx) (tangentFrame y hy)) h1 k1 h2 k2):=by
  unfold pairMixedPhysicalPdf physicalPairScoreDensity
  rw [scorePairTarget_physical_smul,ENNReal.ofReal_mul (by positivity)]
  rfl

theorem source_pair_value_physical_pdf_eq {n P:ℕ} (c:Degree P→ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 h2:ℝ) :
    pairValuePhysicalPdf c x y hx hy (WithLp.toLp 2 (h1,h2))=
      ENNReal.ofReal (physicalPairValueDensity (n+3)
        (residualPairValue c x y (tangentFrame x hx) (tangentFrame y hy)) h1 h2):=by
  unfold pairValuePhysicalPdf physicalPairValueDensity
  rw [valueScorePairTarget_physical_smul,ENNReal.ofReal_mul (by positivity)]
  rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments
