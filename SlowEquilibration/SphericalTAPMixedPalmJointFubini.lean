-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmDensityIdentity

@[expose] public section

/-! Exact real radial/latitude Fubini identity in the physical mixed Palm
numerator. The integrability premise is a standard compact-rectangle bound
on the already-defined joint density. -/

namespace SlowEquilibration.SphericalTAPMixedPalmJointFubini
noncomputable section
open Set MeasureTheory StrongFieldComplexity SphericalModel
open SphericalMarkedWindows SphericalTAPMixedBandExponent
open SphericalTAPMixedPalmDensityIdentity
open SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedPhysicalJointLaplace
open SphericalTAPCriticalEnergyPalmAverage
set_option autoImplicit false

theorem source_mixed_radial_latitude_numerator_eq_joint
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (β e L R q b : ℝ)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1)
    (hJint : IntegrableOn (sourceMixedJointIntegrand d μ β Q e)
      ((Icc L R) ×ˢ (Icc (q-b) (q+b))) planeVolume) :
    (∫ k in Ioo L R,
      (∫ a in Icc (q-b) (q+b),
        (Real.sqrt (1-a^2))^(d-1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) *
        sourceAllCriticalRadialWeight d μ Q e k ∂volume) =
      Real.exp (((d+2:ℕ):ℝ)*
        (Real.log (Q*μ.xi1 Q)/2-1/2)) *
        sourceMixedJointLaplace d μ β Q e L R q b := by
  let T : ℝ := Real.exp (((d+2:ℕ):ℝ)*
    (Real.log (Q*μ.xi1 Q)/2-1/2))
  let U := Icc L R
  let A := Icc (q-b) (q+b)
  let f := sourceMixedJointIntegrand d μ β Q e
  have hpoint (k : ℝ) :
      (∫ a in A,
        (Real.sqrt (1-a^2))^(d-1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) *
        sourceAllCriticalRadialWeight d μ Q e k =
      T * (∫ a in A, f (k,a) ∂volume) := by
    rw [← integral_mul_const,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    have hh := mixed_palm_density_eq_source_joint
      d hd μ hQ β e k a (hband ha)
    dsimp [T,f]
    calc
      ((Real.sqrt (1-a^2))^(d-1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) *
        sourceAllCriticalRadialWeight d μ Q e k =
        sourceAllCriticalRadialWeight d μ Q e k *
          (Real.sqrt (1-a^2))^(d-1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) := by ring
      _ = _ := hh
  have hprod : (∫ k in U, ∫ a in A, f (k,a) ∂volume ∂volume) =
      sourceMixedJointLaplace d μ β Q e L R q b := by
    have hh := setIntegral_prod f hJint
    simpa only [sourceMixedJointLaplace,planeVolume,U,A,f] using hh.symm
  calc
    (∫ k in Ioo L R,
      (∫ a in A,
        (Real.sqrt (1-a^2))^(d-1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) *
        sourceAllCriticalRadialWeight d μ Q e k ∂volume) =
      ∫ k in U,
        (∫ a in A,
          (Real.sqrt (1-a^2))^(d-1) *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) *
          sourceAllCriticalRadialWeight d μ Q e k ∂volume := by
      exact (integral_Icc_eq_integral_Ioo).symm
    _ = ∫ k in U, T*(∫ a in A, f (k,a) ∂volume) ∂volume := by
      apply integral_congr_ae
      filter_upwards with k
      exact hpoint k
    _ = T*(∫ k in U, ∫ a in A, f (k,a) ∂volume ∂volume) :=
      integral_const_mul _ _
    _ = _ := by rw [hprod]

end
end SlowEquilibration.SphericalTAPMixedPalmJointFubini
