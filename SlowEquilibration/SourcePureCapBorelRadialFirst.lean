-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureLatitudeRadialDisintegration
public import SlowEquilibration.SphericalPureOriginalConditionalBandFubini

/-! The exact radial first moment of an arbitrary Borel latitude band for
the original pure critical-point posterior. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelRadialFirst
noncomputable section
open Classical
open Set MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalPureOriginalConditionalBandFubini
open SourcePureLatitudeRadialDisintegration
open SphericalTAPCriticalPureLatitudeVariance
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem latitudeLaw_overlap_ae_all {n : ℕ} (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (q : ℝ) :
    ∀ᵐ w ∂latitudeLaw u (latitudeFrameAt u) q, overlap u w = q := by
  let e := latitudeFrameAt u
  let T := latitudeMap u e q
  have hT : Measurable T := (latitudeMap_continuous u e q).measurable
  have hset : MeasurableSet {w : Vector (n+1) | overlap u w = q} := by
    apply measurableSet_eq_fun
    · exact (by unfold overlap; fun_prop :
        Continuous (fun w : Vector (n+1) => overlap u w)).measurable
    · exact measurable_const
  unfold latitudeLaw
  rw [ae_map_iff hT.aemeasurable hset]
  exact Filter.Eventually.of_forall fun x => by
    change overlap u (latitudeMap u e q x) = q
    rw [show overlap u (latitudeMap u e q x) =
      overlap (latitudeMap u e q x) u by unfold overlap; rw [real_inner_comm]]
    exact overlap_latitude_center u hu e (latitudeFrameAt_orthogonal u hu) q x

def radialMeanWeight (n p : ℕ) (β H : ℝ) (I : Set ℝ) (s : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  if 1-(s : ℝ)^2/2 ∈ I then
    ENNReal.ofReal (Real.exp (β*H*(1-(s : ℝ)^2/2)^p+
      (n+1 : ℕ)*β^2*sourcePureLatitudeVariance p 1 (1-(s : ℝ)^2/2)/2))
  else 0

theorem radialMeanWeight_measurable (n p : ℕ) (β H : ℝ)
    {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable (radialMeanWeight n p β H I) := by
  unfold radialMeanWeight
  apply Measurable.ite
  · exact hI.preimage (by fun_prop : Measurable (fun s : Ioi (0 : ℝ) =>
      1-(s : ℝ)^2/2))
  · exact ENNReal.measurable_ofReal.comp (by
      unfold sourcePureLatitudeVariance
      fun_prop)
  · exact measurable_const

/-- The first moment after radial coarea retains the exact Borel indicator.
This is an identity of finite nonnegative integrals, with no band shape
assumption. -/
theorem original_pure_mean_borel_radial (n p : ℕ) (hn : 2 ≤ n)
    (β H : ℝ) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {I : Set ℝ} (hI : MeasurableSet I) :
    (∫⁻ w : Vector (n+1),
      ENNReal.ofReal ((overlapRegion u I).indicator
        (originalPureMeanProfile n p 1 β H u) w) ∂sphereLaw (n+1)) =
      ∫⁻ s : Ioi (0 : ℝ), radialMeanWeight n p β H I s ∂radialLaw n := by
  have hB : MeasurableSet (overlapRegion u I) := overlapRegion_measurable u hI
  let F : Vector (n+1) → ℝ≥0∞ := fun w => ENNReal.ofReal
    ((overlapRegion u I).indicator (originalPureMeanProfile n p 1 β H u) w)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    ((originalPureMeanProfile_continuous n p 1 β H u).measurable.indicator hB)
  rw [show (∫⁻ w : Vector (n+1),
      ENNReal.ofReal ((overlapRegion u I).indicator
        (originalPureMeanProfile n p 1 β H u) w) ∂sphereLaw (n+1)) =
      ∫⁻ w, F w ∂sphereLaw (n+1) from rfl,
    sphereLaw_lintegral_radialLaw hn u hu F hF]
  apply lintegral_congr
  intro s
  let q : ℝ := 1-(s : ℝ)^2/2
  have heq : ∀ᵐ w ∂latitudeLaw u (latitudeFrameAt u) q,
      F w = if q ∈ I then ENNReal.ofReal
        (Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*
          sourcePureLatitudeVariance p 1 q/2)) else 0 := by
    filter_upwards [latitudeLaw_overlap_ae_all u hu q] with w hw
    have hw' : overlap w u = q := by
      rw [show overlap w u = overlap u w by unfold overlap; rw [real_inner_comm],hw]
    by_cases hq : q ∈ I
    · have hmem : w ∈ overlapRegion u I := by simpa [overlapRegion,hw'] using hq
      simp only [hq,ite_true]
      change ENNReal.ofReal ((overlapRegion u I).indicator
        (originalPureMeanProfile n p 1 β H u) w) = _
      rw [Set.indicator_of_mem hmem]
      simp only [originalPureMeanProfile,hw]
    · have hnot : w ∉ overlapRegion u I := by simpa [overlapRegion,hw'] using hq
      simp only [hq,ite_false]
      change ENNReal.ofReal ((overlapRegion u I).indicator
        (originalPureMeanProfile n p 1 β H u) w) = _
      rw [Set.indicator_of_notMem hnot]
      simp
  rw [lintegral_congr_ae heq,lintegral_const]
  simp only [measure_univ,mul_one]
  rfl

end
end SlowEquilibration.SourcePureCapBorelRadialFirst
