-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureSourceQuadraticPhysical
public import SlowEquilibration.SphericalTAPPureQuadraticRealTransfer
public import SlowEquilibration.SphericalTAPPurePalmBandShrink
public import SlowEquilibration.SphericalTAPCriticalPureBandScaleIdentity

@[expose] public section

/-! The exact determinant-weighted original-band ratio under the pure
energy Palm law, and its reduction to the genuine pure latitude Laplace
integral. -/

namespace SlowEquilibration.SphericalTAPPurePalmSourceUpper
noncomputable section
open Set MeasureTheory Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPPureQuadraticRealTransfer
open SphericalTAPPurePalmLaplaceBridge
open SphericalTAPPurePalmBandShrink
open SphericalQuadraticLatitudeJetCovariance
open SphericalTAPCriticalPureBandScaleIdentity
open GOEPhysicalPotential
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The literal proper-pure all-critical Palm expectation of the original
restricted band partition, with the actual intrinsic-determinant weight. -/
def sourcePureEnergyPalmBandExpectation
    (d p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q β e q b : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) : ℝ :=
  let μ := FiniteMixture.pure p hp alpha halpha
  (∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂pureLaw p hp alpha halpha Q u hu e) /
    (∫ J, intrinsicDet μ Q u J
      ∂pureLaw p hp alpha halpha Q u hu e)

/-- The true physical section and coarea identities bound the normalized
proper-pure Palm band by any upper bound on its printed latitude Laplace
integral. No independence between determinant and quadratic bank is used. -/
theorem pure_palm_band_upper_of_sections
    (d : ℕ) (hd : 1 ≤ d)
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q β e q b C T : ℝ) (hb : 0 < b) (hC : 0 ≤ C)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hdet : 0 < ∫ J, intrinsicDet (FiniteMixture.pure p hp alpha halpha)
      Q u J ∂pureLaw p hp alpha halpha Q u hu e)
    (hMean : (∫ J, intrinsicDet (FiniteMixture.pure p hp alpha halpha)
      Q u J ∂pureLaw p hp alpha halpha Q u hu e) =
        physicalMean d (d+2)
          (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q) ((p:ℝ)*e))
    (hquad : let μ := FiniteMixture.pure p hp alpha halpha
      ∀ a ∈ Icc (q-b) (q+b),
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J))
        (pureLaw p hp alpha halpha Q u hu e) ∧
      (∫ J, intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J)
        ∂pureLaw p hp alpha halpha Q u hu e) ≤
      C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a)))
    (hLap : (∫ a in Icc (q-b) (q+b),
      (1-a^2)^(-(3/2:ℝ)) *
        Real.exp (((d+2:ℕ):ℝ)*
          sourcePureLatitudeExponent p alpha Q β e a)) ≤ T) :
    sourcePureEnergyPalmBandExpectation d p hp alpha halpha Q β e q b u hu ≤
      C*(latitudeNormalization (d+1)).toReal*T := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let D := ∫ J, intrinsicDet μ Q u J ∂ν
  let Z := ∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b))) ∂ν
  have hReal := pure_quadratic_real_sections_to_band
    d hd p hp alpha halpha Q β e q b C hb hC hband u hu hquad
  dsimp only at hReal
  have hEq := pure_palm_weighted_density_eq_laplace_integral
    d hd p alpha Q β e q b C
      (physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e))
    (fun a ha => ⟨by linarith [(hband ha).1],(hband ha).2⟩)
  rw [hEq] at hReal
  have hLat : 0 ≤ (latitudeNormalization (d+1)).toReal := ENNReal.toReal_nonneg
  have hCD : 0 ≤ C*D := mul_nonneg hC hdet.le
  have hMean' : D = physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) := hMean
  have hZ : Z ≤ (latitudeNormalization (d+1)).toReal*(C*D*T) := by
    calc
      Z ≤ (latitudeNormalization (d+1)).toReal *
          (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
            (∫ a in Icc (q-b) (q+b),
              (1-a^2)^(-(3/2:ℝ)) *
                Real.exp (((d+2:ℕ):ℝ)*
                  sourcePureLatitudeExponent p alpha Q β e a))) := by
            simpa only [Z,ν,μ] using hReal.2
      _ = (latitudeNormalization (d+1)).toReal *
          (C*D*(∫ a in Icc (q-b) (q+b),
            (1-a^2)^(-(3/2:ℝ)) *
              Real.exp (((d+2:ℕ):ℝ)*
                sourcePureLatitudeExponent p alpha Q β e a))) := by rw [hMean']
      _ ≤ (latitudeNormalization (d+1)).toReal*(C*D*T) := by gcongr
  change Z/D ≤ C*(latitudeNormalization (d+1)).toReal*T
  apply (div_le_iff₀ hdet).mpr
  calc
    Z ≤ (latitudeNormalization (d+1)).toReal*(C*D*T) := hZ
    _ = C*(latitudeNormalization (d+1)).toReal*T*D := by ring

end
end SlowEquilibration.SphericalTAPPurePalmSourceUpper
