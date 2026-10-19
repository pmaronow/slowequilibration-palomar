-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalCountProbabilityLimits

/-! The literal retained physical-window count vanishes when the original
global maximum lies below that window. This is the deterministic implication
used for source 11.14's lower tail. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set MeasureTheory
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open SphericalForm
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem source_retained_window_zero_of_max_below
    (n : ℕ) (μ : FiniteMixture) (Q l r κ C ε η E G : ℝ)
    (U : Set ℝ) (J : Disorder (n+3) μ.maxDegree)
    (hmax : sourceSphereMaximum (n+1) μ Q J < l) :
    sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc l r) U) κ C ε η E G J = 0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨y,hy,_hcrit,hupper,heq⟩ := sourceSphereMaximum_attained (n+1) μ Q J
  have hempty :
      {u : Vector ((n+2)+1) | ‖u‖^2=((n+2)+1:ℕ) ∧
        surfaceGradient (field c J) u=0 ∧
        actualScore c J u ∈ physicalEnergyWindow (n+3) (Icc l r) U} = ∅ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hu,_,hwin⟩
    have hfield := (actualScore_mem_physicalEnergyWindow (by omega) c J u (Icc l r) U).mp hwin
    have hle : field c J u ≤ sourceSphereMaximum (n+1) μ Q J := by
      rw [heq]
      exact hupper hu
    exact (not_le_of_gt hmax) (hfield.1.1.trans hle)
  unfold sourceRetainedScoreWindowCount actualScoreWindowCount
  change (∑' u : {u : Vector ((n+2)+1) | ‖u‖^2=((n+2)+1:ℕ) ∧
    surfaceGradient (field c J) u=0 ∧
    actualScore c J u ∈ physicalEnergyWindow (n+3) (Icc l r) U},
    sourceSelectionMark c κ C ε η E G J u) = 0
  rw [hempty]
  exact tsum_empty

/-- A nonzero retained count supplies an actual ordinary critical point
in the source energy/radial window. No finiteness or Morse genericity is
needed for this one-way implication. -/
theorem source_retained_nonzero_critical_window_nonempty
    (n : ℕ) (μ : FiniteMixture) (Q l r κ C ε η E G : ℝ)
    (U : Set ℝ) (J : Disorder (n+3) μ.maxDegree)
    (hret : (sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc l r) U)
      κ C ε η E G J).toReal ≠ 0) :
    Set.Nonempty {u : Vector (n+3) | ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈ Icc l r ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U} := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A : Set (Vector ((n+2)+1)) := {u | ‖u‖^2=((n+2)+1:ℕ) ∧
    surfaceGradient (field c J) u=0 ∧
    actualScore c J u ∈ physicalEnergyWindow (n+3) (Icc l r) U}
  have hA : A.Nonempty := by
    by_contra hne
    have hempty : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : sourceRetainedScoreWindowCount (n+2) c
        (physicalEnergyWindow (n+3) (Icc l r) U)
        κ C ε η E G J=0 := by
      unfold sourceRetainedScoreWindowCount actualScoreWindowCount
      change (∑' u : A,sourceSelectionMark c κ C ε η E G J u)=0
      rw [hempty]
      exact tsum_empty
    exact hret (by rw [hzero];rfl)
  obtain ⟨u,hu⟩ := hA
  refine ⟨u,hu.1,hu.2.1,?_⟩
  exact (actualScore_mem_physicalEnergyWindow (by omega) c J u (Icc l r) U).mp hu.2.2

end
end SlowEquilibration.PairConditionalDeterminantMoments
