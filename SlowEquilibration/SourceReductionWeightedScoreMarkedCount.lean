-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceReductionWeightedFiberBorel
public import SlowEquilibration.SourceReductionWindowCenterScoreEquiv
public import SlowEquilibration.SourceReductionFiniteCentersAE

/-! The literal weighted critical-center score is exactly the marked
Kac--Rice count whenever its original-tensor center fiber is finite. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionWeightedScoreMarkedCount
open Set MeasureTheory ProbabilityTheory SphericalModel
open SphericalGaussianJet SphericalMarkedWindows
open SphericalForm
open SourceReductionClosedBandGraph SourceReductionFinitePathUnionBound
open SourceReductionWindowCenterScoreEquiv
open SourceReductionWeightedCenterScore
open SourceReductionFiniteCentersAE
open ConditionedEntrance
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.style.haveILetI false

variable {N : ℕ}

private theorem finite_set_sum_coe {α : Type*} (s : Set α) [Fintype s]
    (f : α → ℝ≥0∞) :
    ∑ x ∈ s.toFinset, f x = ∑ x : s, f x.1 := by
  classical
  simp [Set.toFinset]

theorem actualWindowCenterWeightedHitSum_eq_actualScoreWindowCount_of_finite
    (d : ℕ) (μ : FiniteMixture) (Q m M a β : ℝ)
    (U : Set ℝ) (T : ℝ≥0) (J : Disorder (d+2) μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    actualWindowCenterWeightedHitSum μ Q m M a β U T J =
      actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (d+2) (Icc (m-M) (m+M)) U)
        (fun _ u => ENNReal.ofReal
          (originalTrueCapHitProbability μ β T a u J)) J := by
  classical
  let s := physicalWindowCenters μ Q m M U J
  have hs : s.Finite := physicalWindowCenters_finite μ Q m M U J hfinite
  let A : Set (Vector (d+2)) :=
    {u | ‖u‖^2=((d+2:ℕ):ℝ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
        physicalEnergyWindow (d+2) (Icc (m-M) (m+M)) U}
  let e : s ≃ A := physicalWindowCentersScoreEquiv
    (by omega : d+2 ≠ 0) μ Q m M U J
  letI : Fintype s := hs.fintype
  letI : Fintype A := Fintype.ofEquiv s e
  rw [actualWindowCenterWeightedHitSum_of_finite μ Q m M a β U T J hfinite]
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

theorem actualWindowCenterWeightedHitSum_ae_eq_actualScoreWindowCount
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (m M a β : ℝ) (U : Set ℝ) (T : ℝ≥0) :
    ∀ᵐ J ∂disorderLaw (d+2) μ.maxDegree,
      actualWindowCenterWeightedHitSum μ Q m M a β U T J =
        actualScoreWindowCount (d+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (d+2) (Icc (m-M) (m+M)) U)
          (fun J u => ENNReal.ofReal
            (originalTrueCapHitProbability μ β T a u J)) J := by
  exact (windowCenters_finite_ae d μ hQ m M U).mono fun J hfinite => by
    have h := actualWindowCenterWeightedHitSum_eq_actualScoreWindowCount_of_finite
      d μ Q m M a β U T J hfinite
    convert h using 1
    unfold actualScoreWindowCount
    apply tsum_congr
    intro u
    rfl

end SlowEquilibration.SourceReductionWeightedScoreMarkedCount
