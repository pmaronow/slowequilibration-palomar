-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDoubleLatitudeThickening

/-! Actual transverse Taylor-band thickening, with the exact entropy
log(1-Q)/2, derived from genuine nested latitude coarea. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTaylorRemainder
open MeasureTheory Set Filter Metric InnerProductSpace
open SphericalModel SphericalNestedLatitude
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A literal transverse-band partition for any differentiable ambient H
thickens into actual positive spherical volume. This also accepts the actual
planted translated Hamiltonian with its independently proved gradient bound. -/
theorem transverseBand_partitionOn_eventually_lower_of_gradient_bound
    {Q q β K ε : ℝ} (hQ : Q∈Ioo (0:ℝ) 1) (hq : |q|<1)
    (hK : 0 ≤ K) (hε : 0<ε) {A : Set ℝ} (hA : IsOpen A)
    (hrA : bandOuterLatitude Q q∈A) :
    ∀ᶠ n : ℕ in atTop,∀ (H : Vector (n+2) → ℝ),Differentiable ℝ H →
      (∀ x ∈ closedBall 0 (Real.sqrt (n+2:ℕ)),‖fderiv ℝ H x‖ ≤ K*Real.sqrt (n+2:ℕ)) →
      ∀ (w : Vector (n+2)),‖w‖^2=(n+2:ℕ) → ∀ (y : Vector (n+1)),‖y‖^2=(n+1:ℕ) → ∀ (B : ℝ),
      B ≤ Real.log (partition n β (fun z => H
        (transverseBandPoint (latitudeMap w (latitudeFrameAt w) q y)
          (bottomTransverseFrame (latitudeFrameAt w) y) Q z)))/((n+2:ℕ):ℝ) →
      Real.exp (((n+2:ℕ):ℝ)*(B+Real.log (1-Q)/2-ε)) ≤
        partitionOn β H (overlapRegion w A) := by
  have ht := bandInnerLatitude_mem hQ hq
  have hta : |bandInnerLatitude Q q|<1 := by rw [abs_of_pos ht.1];exact ht.2
  filter_upwards [nestedLatitude_partitionOn_eventually_lower
    (β := β) (bandOuterLatitude_abs_lt hQ hq) hta hK hε hA hrA,eventually_ge_atTop 1] with n hn hn1
  intro H hH hgrad w hw y hy B hB
  have he : (fun z : Vector n => H (transverseBandPoint (latitudeMap w (latitudeFrameAt w) q y)
      (bottomTransverseFrame (latitudeFrameAt w) y) Q z))=
      fun z => H (nestedLatitude w y (bandOuterLatitude Q q) (bandInnerLatitude Q q) z) := by
    funext z
    rw [transverseBandPoint_eq_nestedLatitude hn1 hQ hq]
    rfl
  rw [he] at hB
  have hh := hn H hH hgrad w hw y hy B hB
  rwa [band_latitude_entropy_log hQ hq] at hh

/-- The original finite-mixture tensor field satisfies the deterministic
thickening premise on its actual regular-disorder event. No additional
thickening event or partition lower estimate is assumed. -/
theorem regularDisorder_transverseBand_partitionOn_eventually_lower
    (μ : FiniteMixture) {Q q β ε : ℝ} (hQ : Q∈Ioo (0:ℝ) 1) (hq : |q|<1)
    (hε : 0<ε) {A : Set ℝ} (hA : IsOpen A) (hrA : bandOuterLatitude Q q∈A) :
    ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+2)),‖w‖^2=(n+2:ℕ) →
      ∀ (y : Vector (n+1)),‖y‖^2=(n+1:ℕ) → ∀ (J : Disorder (n+2) μ.maxDegree),J∈regularDisorder →
      ∀ (B : ℝ), B ≤ transverseBandPressure μ w (latitudeFrameAt w) q Q β J y →
        Real.exp (((n+2:ℕ):ℝ)*(B+Real.log (1-Q)/2-ε)) ≤
          partitionOn β (fieldOfMixture μ J) (overlapRegion w A) := by
  let c := mixtureCoefficients μ
  filter_upwards [transverseBand_partitionOn_eventually_lower_of_gradient_bound
    (β := β) hQ hq (derivativeConstant_pos c).le hε hA hrA] with n hn
  intro w hw y hy J hJ B hB
  apply hn (fieldOfMixture μ J) ((field_contDiff c J).differentiable (by simp)) ?_ w hw y hy B hB
  intro x hx
  have hg := (field_regularDisorder_ball_bounds (show 1≤n+2 by omega) c J hJ x
    (by simpa only [mem_closedBall,dist_zero_right] using hx)).2.1
  change ‖fderiv ℝ (field c J) x‖ ≤ derivativeConstant c * Real.sqrt (n+2:ℕ)
  simpa only [gradient,LinearIsometryEquiv.norm_map] using hg

end SlowEquilibration.SphericalTaylorRemainder
