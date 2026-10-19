-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceReductionWindowCenterScoreEquiv
public import SlowEquilibration.SourceMixedCenteredTrueEntranceTransfer

/-! The first inequality of manuscript Proposition `cp-transfer`, from the
literal original Brownian path-hit union to the actual marked critical sum. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionCPPathBound
open Set MeasureTheory ProbabilityTheory SphericalModel
open SphericalMarkedWindows SphericalRotationCovariance SphericalGaussianJet
open SphericalForm
open SphericalFieldKernels SphericalKacRiceHittingSource
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open SourceReductionFinitePathUnionBound
open SourceReductionTrueCapPathWeight SourceReductionWindowCenterScoreEquiv
open ConditionedEntrance
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

private theorem finite_set_sum_coe {α : Type*} (s : Set α) [Fintype s]
    (f : α → ℝ≥0∞) :
    ∑ x ∈ s.toFinset, f x = ∑ x : s, f x.1 := by
  classical
  simp [Set.toFinset]

private theorem physical_center_mark_sum_eq_actual_score_count
    (d : ℕ) (μ : FiniteMixture) (Q m M a β : ℝ)
    (U : Set ℝ) (T : ℝ≥0) (J : Disorder (d+2) μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    ∑ u ∈ (physicalWindowCenters_finite μ Q m M U J hfinite).toFinset,
      ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J) =
      actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (d+2) (Icc (m-M) (m+M)) U)
        (fun _ u => ENNReal.ofReal (originalTrueCapHitProbability μ β T a u J)) J := by
  classical
  let s := physicalWindowCenters μ Q m M U J
  have hs : s.Finite := physicalWindowCenters_finite μ Q m M U J hfinite
  let A : Set (Vector (d+2)) :=
    {u | ‖u‖^2=((d+2:ℕ):ℝ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
        physicalEnergyWindow (d+2) (Icc (m-M) (m+M)) U}
  let e : s ≃ A := physicalWindowCentersScoreEquiv (by omega) μ Q m M U J
  letI : Fintype s := hs.fintype
  letI : Fintype A := Fintype.ofEquiv s e
  have hsum : ∑ u ∈ hs.toFinset,
      ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J) =
      ∑ u : s, ENNReal.ofReal
        (originalTrueCapHitProbability μ β T a u.1.1 J) := by
    rw [hs.toFinset_eq_toFinset]
    exact finite_set_sum_coe s _
  rw [hsum]
  unfold actualScoreWindowCount
  change (∑ u : s, ENNReal.ofReal
      (originalTrueCapHitProbability μ β T a u.1.1 J)) =
    ∑' u : A, ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J)
  rw [tsum_fintype]
  have he (u : s) : (e u).1 = u.1.1 := by rfl
  simpa only [he] using
    (e.sum_comp (fun u : A =>
      ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J)))

/-- At every disorder with finitely many selected critical centers, the
original diffusion's probability of hitting any selected cap is bounded by
the exact marked score-window Kac--Rice random variable. -/
theorem actualWindowPathHitProbability_le_actual_marked_count
    (d : ℕ) (μ : FiniteMixture) (Q m M a β : ℝ)
    (U : Set ℝ) (T : ℝ≥0) (J : Disorder (d+2) μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    ENNReal.ofReal
      (actualWindowPathHitProbability (by omega : 2 ≤ d+2)
        μ Q m M a β U T J) ≤
      actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (d+2) (Icc (m-M) (m+M)) U)
        (fun _ u => ENNReal.ofReal (originalTrueCapHitProbability μ β T a u J)) J := by
  let hs := physicalWindowCenters_finite μ Q m M U J hfinite
  have hunion := actualWindowPathHitProbability_le_sum
    (by omega : 2 ≤ d+2) μ Q m M a β U T J hfinite
  calc
    ENNReal.ofReal
        (actualWindowPathHitProbability (by omega : 2 ≤ d+2)
          μ Q m M a β U T J) ≤
        ENNReal.ofReal
          (∑ u ∈ hs.toFinset,
            ((uniformRealPathKernel (by omega : 2 ≤ d+2) μ β T (fieldMap μ J)).real
              {p | (p,u) ∈ overlapSupEvent T a})) :=
      ENNReal.ofReal_le_ofReal hunion
    _ = ∑ u ∈ hs.toFinset,
          ENNReal.ofReal
            ((uniformRealPathKernel (by omega : 2 ≤ d+2) μ β T (fieldMap μ J)).real
              {p | (p,u) ∈ overlapSupEvent T a}) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro u hu
      exact measureReal_nonneg
    _ = ∑ u ∈ hs.toFinset,
          ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact congrArg ENNReal.ofReal
        (uniformRealPathKernel_original_true_cap_probability
          (by omega : 2 ≤ d+2) μ β T a J u)
    _ = _ := physical_center_mark_sum_eq_actual_score_count
      d μ Q m M a β U T J hfinite

end SlowEquilibration.SourceReductionCPPathBound
