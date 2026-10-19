-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1ProcessRotation
public import SlowEquilibration.SphericalSmoothParameterCapHit

/-! Actual finite-horizon cap-hit probability covariance for jointly smooth
families of spherical Langevin gradients. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalSmoothParameter SphericalWienerRotation
open SphericalAging SphericalAging.HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {N : ℕ}
  {Θ Θ' : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [FiniteDimensional ℝ Θ] [MeasurableSpace Θ] [BorelSpace Θ]
  [NormedAddCommGroup Θ'] [NormedSpace ℝ Θ']
  [FiniteDimensional ℝ Θ'] [MeasurableSpace Θ'] [BorelSpace Θ']

theorem capHitProbability_rotation_at
    (hN : N ≠ 0) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (β : ℝ) (g : Θ × Vector N → Vector N)
    (hg : ContDiff ℝ 1 g)
    (g' : Θ' × Vector N → Vector N)
    (hg' : ContDiff ℝ 1 g')
    (θ : Θ) (θ' : Θ')
    (hgrad : ∀ v, g' (θ',U v) = U (g (θ,v)))
    (u x : Vector N) (hx : OnSphere x)
    (T : ℝ≥0) (α : ℝ) :
    capHitProbability β g' hg' T α (U u,(θ',U x)) =
      capHitProbability β g hg T α (u,(θ,x)) := by
  let P := VectorBrownian.law N
  let hφ := rotateWiener_measurePreserving U
  let pL (ω : VectorBrownian.Space N) :=
    SphericalSmoothParameter.jointContinuousPath β g hg T ((θ,x),ω)
  let pR (ω : VectorBrownian.Space N) :=
    SphericalSmoothParameter.jointContinuousPath β g' hg' T ((θ',U x),ω)
  let EL : Set (VectorBrownian.Space N) :=
    {ω | α ≤ pathMaximumOverlap T (u,pL ω)}
  let ER : Set (VectorBrownian.Space N) :=
    {ω | α ≤ pathMaximumOverlap T (U u,pR ω)}
  have hER : MeasurableSet ER := by
    apply measurableSet_le measurable_const
    exact (pathMaximumOverlap_continuous T).measurable.comp
      (measurable_const.prodMk
        ((SphericalSmoothParameter.jointContinuousPath_measurable β g' hg' T).comp
          (measurable_const.prodMk measurable_id)))
  have hrot := c1Process_rotated_ae hN U β
    (fun y => g (θ,y)) (fun y => g' (θ',y))
    (hg.comp (contDiff_const.prodMk contDiff_id))
    (hg'.comp (contDiff_const.prodMk contDiff_id))
    hgrad x hx T
  have hleft := hφ.quasiMeasurePreserving.ae
    (SphericalSmoothParameter.jointContinuousPath_ae_actual β g' hg' T (θ',U x))
  have hright := SphericalSmoothParameter.jointContinuousPath_ae_actual β g hg T (θ,x)
  have hevent : ∀ᵐ ω ∂P, ω ∈ rotateWiener U ⁻¹' ER ↔ ω ∈ EL := by
    filter_upwards [hleft,hright,hrot] with ω hleft hright hrot
    have hpath : ∀ t : PathTime T,
        pR (rotateWiener U ω) t = U (pL ω t) := by
      intro t
      rw [hleft t,hrot t.1 t.2.2,hright t]
    have hsame : pathMaximumOverlap T (U u,pR (rotateWiener U ω)) =
        pathMaximumOverlap T (u,pL ω) := by
      apply congrArg SphericalParisiContinuousMaximum.maximum
      apply ContinuousMap.ext
      intro t
      change |overlap (U u) (pR (rotateWiener U ω) t)| =
        |overlap u (pL ω t)|
      rw [hpath t]
      simp only [overlap,U.inner_map_map]
    change α ≤ pathMaximumOverlap T (U u,pR (rotateWiener U ω)) ↔
      α ≤ pathMaximumOverlap T (u,pL ω)
    rw [hsame]
  change P.real ER = P.real EL
  change (P ER).toReal = (P EL).toReal
  rw [← hφ.measure_preimage hER.nullMeasurableSet]
  exact congrArg ENNReal.toReal
    (measure_congr (hevent.mono (fun _ h => propext h)))

end SlowEquilibration.SphericalRotationCovariance
