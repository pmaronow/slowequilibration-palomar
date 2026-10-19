-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedEnergyPalmRatioBridge
public import SlowEquilibration.SphericalTAPMixedJointCompactIntegrable

@[expose] public section

/-! The physical mixed Palm radial average exactly yields the manuscript's
`c_N^lat J_N/I_N` ratio. Compact integrability and Fubini are proved, so the
remaining premises are the fixed-mark bound and its radial integrability. -/

namespace SlowEquilibration.SphericalTAPMixedEnergyPalmCoareaRatio
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedPhysicalRadialLower
open SphericalTAPMixedBandExponent
open SphericalTAPMixedEnergyPalmRatioBridge
open SphericalTAPMixedJointCompactIntegrable
open SphericalTAPMixedPalmJointFubini
set_option autoImplicit false

theorem mixed_energy_palm_coarea_ratio
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b C : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R) (hb : 0 < b)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) :
    let ρ := sourceAllCriticalRadialLaw d μ Q e L R
    let M := fun k : ℝ =>
      (∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))
    let G := fun k : ℝ => ∫ a in Icc (q-b) (q+b),
      (Real.sqrt (1-a^2))^(d-1) *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume
    Integrable M ρ → Integrable G ρ →
    (∀ k ∈ Ioo L R, M k ≤
      C*(latitudeNormalization (d+1)).toReal*G k) →
    sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu ≤
      C*(latitudeNormalization (d+1)).toReal *
        (sourceMixedJointLaplace d μ β Q e L R q b /
          sourceMixedRadialLaplace d μ Q e L R) := by
  dsimp only
  intro hMInt hGInt hmark
  have hband' : Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 := by
    intro a ha
    have hh := hband ha
    exact ⟨by linarith [hh.1],hh.2⟩
  have hJint := sourceMixedJointIntegrand_integrableOn_compact
    d μ hQ β e L R q b hEdge hLR hb hband
  have hNum := source_mixed_radial_latitude_numerator_eq_joint
    d hd μ hQ β e L R q b hband' hJint
  exact mixed_energy_palm_coarea_ratio_of_fixed_marks
    d μ hQ β e L R q b C hEdge hLR u hu
    hMInt hGInt hmark hNum

end
end SlowEquilibration.SphericalTAPMixedEnergyPalmCoareaRatio
