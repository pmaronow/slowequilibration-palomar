-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorNestedLatitude

@[expose] public section

/-! The actual planted Gaussian translate adds exactly its overlap
covariance to the original physical transverse-band pressure. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem transverseBandPoint_continuous {N d : ℕ} (m : Vector N)
    (e : Vector d →ₗᵢ[ℝ] Vector N) (Q : ℝ) :
    Continuous (transverseBandPoint m e Q) := by
  unfold transverseBandPoint transverseOffset
  exact (continuous_const.add (e.continuous.const_smul (Real.sqrt ((N : ℝ)*(1-Q)/(Q*(d : ℝ)))))).const_smul (Real.sqrt Q)

theorem transverseBandPressure_plantedShift {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) (Q q β : ℝ) (w : Vector (n+2))
    (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ z,inner ℝ (e z) w=0)
    (J : Disorder (n+2) μ.maxDegree) (y : Vector (n+1)) :
    transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y=
      transverseBandPressure μ w e q Q β J y+β^2*μ.xi (bandOuterLatitude Q q) := by
  let m := latitudeMap w e q y
  let l := bottomTransverseFrame e y
  let H : Vector n → ℝ := fun z => fieldOfMixture μ J (transverseBandPoint m l Q z)
  have hH : Continuous H := (field_contDiff (mixtureCoefficients μ) J).continuous.comp
    (transverseBandPoint_continuous m l Q)
  have hfield (z : Vector n) :
      fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β w) (transverseBandPoint m l Q z)=
        β*((n+2 : ℕ) : ℝ)*μ.xi (bandOuterLatitude Q q)+H z := by
    rw [fieldOfMixture,field_add_plantedShift (by omega) _ (mixtureCoefficients_nonnegative μ),
      covariancePolynomial_mixture,transverseBandPoint_reference_overlap w m l
        (bottomTransverseFrame_reference_orthogonal w e he y)]
    have ho : overlap m w=q := overlap_latitude_center w hw e he q y
    rw [ho]
    change H z+β*((n+2 : ℕ) : ℝ)*μ.xi (Real.sqrt Q*q)=_
    change H z+β*((n+2 : ℕ) : ℝ)*μ.xi (Real.sqrt Q*q)=
      β*((n+2 : ℕ) : ℝ)*μ.xi (Real.sqrt Q*q)+H z
    ring
  have hchange := congrArg (fun f : Vector n → ℝ => Real.log (partition n β f)/((n+2 : ℕ) : ℝ)) (funext hfield)
  change transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y=
    Real.log (partition n β (fun z => β*((n+2 : ℕ) : ℝ)*μ.xi (bandOuterLatitude Q q)+H z))/((n+2 : ℕ) : ℝ) at hchange
  rw [hchange]
  rw [spherical_logPartition_add_constant hn β _ H hH]
  change (β*(β*((n+2 : ℕ) : ℝ)*μ.xi (bandOuterLatitude Q q))+Real.log (partition n β H))/
    ((n+2 : ℕ) : ℝ)=Real.log (partition n β H)/((n+2 : ℕ) : ℝ)+_
  field_simp
  ring

end
end SlowEquilibration.SphericalTaylorRemainder
