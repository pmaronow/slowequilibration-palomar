-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeTransport

/-! Genuine any-axis latitude averaging transports a proved latitude bound
to the original uniform-sphere integral, retaining the true coarea density. -/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

theorem latitude_average_domination {n : ℕ} (hn : 2 ≤ n)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ))
    (F : Vector (n+1)→ℝ≥0∞) (hF : Measurable F) (G : ℝ→ℝ≥0∞) (hG : Measurable G)
    (hLat : ∀ r ∈ Ioo (-1:ℝ) 1,
      (∫⁻ u,F u ∂latitudeLaw x (latitudeFrameAt x) r) ≤ G r) :
    (∫⁻ u,F u ∂sphereLaw (n+1)) ≤
      ∫⁻ u,G (overlap x u) ∂sphereLaw (n+1) := by
  have hObs : Measurable (fun u : Vector (n+1)=>G (overlap x u)) :=
    hG.comp ((continuous_const.inner continuous_id).div_const ((n+1:ℕ):ℝ)).measurable
  rw [sphereLaw_lintegral_latitudeLaw_at hn x hx F hF,
    sphereLaw_lintegral_latitudeLaw_at hn x hx _ hObs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply lintegral_mono
  intro s
  by_cases hs : s ∈ {s : Ioi (0:ℝ) | (s:ℝ) < 2}
  · rw [indicator_of_mem hs,indicator_of_mem hs]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hr : 1-(s:ℝ)^2/2 ∈ Ioo (-1:ℝ) 1 := by
      change (s:ℝ) < 2 at hs
      have hsp : 0 < (s:ℝ) := s.property
      have hs2 : (s:ℝ)^2 < 4 := by
        nlinarith [mul_pos (show 0 < 2-(s:ℝ) by linarith) (show 0 < 2+(s:ℝ) by linarith)]
      constructor <;> linarith [sq_pos_of_pos hsp]
    have hq : |1-(s:ℝ)^2/2| ≤ 1 := abs_le.mpr ⟨hr.1.le,hr.2.le⟩
    have hmean : (∫⁻ u,G (overlap x u) ∂latitudeLaw x (latitudeFrameAt x) (1-(s:ℝ)^2/2))=
        G (1-(s:ℝ)^2/2) := by
      have he : (fun u=>G (overlap x u)) =ᵐ[latitudeLaw x (latitudeFrameAt x) (1-(s:ℝ)^2/2)]
          fun _=>G (1-(s:ℝ)^2/2) := by
        filter_upwards [latitudeLaw_support (by omega : 1 ≤ n) x hx (latitudeFrameAt x)
          (latitudeFrameAt_orthogonal x hx) hq] with u hu
        have ho : overlap x u=overlap u x := by unfold overlap;rw [real_inner_comm]
        rw [ho,hu.2]
      rw [lintegral_congr_ae he]
      simp
    exact (hLat _ hr).trans_eq hmean.symm
  · simp only [indicator_of_notMem hs,le_refl]

end
end SlowEquilibration.SphericalModel
