-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedEnergyPalmQuadraticReduction

@[expose] public section

/-! Transfer the real determinant–latitude section estimate to the exact
ENNReal form consumed by the physical Palm coarea theorem. The integrability
premise records what is required to interpret the real section integral. -/

namespace SlowEquilibration.SphericalTAPMixedQuadraticRealTransfer
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open GOEPhysicalPotential SphericalTAPMixedBandExponent
open SphericalTAPMixedEnergyPalmQuadraticReduction
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedPhysicalRadialLower
set_option autoImplicit false

theorem mixed_quadratic_real_sections_to_energy_palm
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β e L R q b C : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R) (hb : 0 < b) (hC : 0 ≤ C)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hquad : ∀ k ∈ Ioo L R, ∀ a ∈ Icc (q-b) (q+b),
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J))
        (mixedLaw μ Q u hu (scorePairEquiv (e,k))) ∧
      (∫ J, intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J)
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) :
    sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu ≤
      C*(latitudeNormalization (d+1)).toReal *
        (sourceMixedJointLaplace d μ β Q e L R q b /
          sourceMixedRadialLaplace d μ Q e L R) := by
  apply mixed_energy_palm_upper_of_quadratic_sections d hd μ hQ hnp
    β e L R q b C hEdge hLR hb hC hband u hu
  intro k hk a ha
  obtain ⟨hInt,hLe⟩ := hquad k hk a ha
  have hNonneg : ∀ J : Disorder (d+2) μ.maxDegree,
      0 ≤ intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J) := by
    intro J
    apply mul_nonneg (abs_nonneg _)
    unfold partitionAgainst
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (.of_forall hNonneg)]
  exact ENNReal.ofReal_le_ofReal hLe

end
end SlowEquilibration.SphericalTAPMixedQuadraticRealTransfer
