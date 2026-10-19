-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorNestedLatitude
public import SlowEquilibration.SphericalLatitudeRegularDisorder

/-! Genuine two-latitude continuity from an ambient gradient bound. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalNestedLatitude
open MeasureTheory Set Metric
open SphericalModel
open scoped InnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def nestedLatitude {n : ℕ} (w : Vector (n+2)) (y : Vector (n+1)) (r t : ℝ) (z : Vector n) : Vector (n+2) :=
  latitudeMap w (latitudeFrameAt w) r (latitudeMap y (latitudeFrameAt y) t z)

lemma nestedLatitude_continuous {n : ℕ} (w : Vector (n+2)) (y : Vector (n+1)) (r t : ℝ) :
    Continuous (nestedLatitude w y r t) :=
  (latitudeMap_continuous _ _ _).comp (latitudeMap_continuous _ _ _)

lemma nestedLatitude_norm_sq {n : ℕ} (hn : 1 ≤ n)
    (w : Vector (n+2)) (hw : ‖w‖^2=(n+2:ℕ)) (y : Vector (n+1)) (hy : ‖y‖^2=(n+1:ℕ))
    {r t : ℝ} (hr : |r| ≤ 1) (ht : |t| ≤ 1) (z : Vector n) (hz : ‖z‖^2=(n:ℝ)) :
    ‖nestedLatitude w y r t z‖^2=(n+2:ℕ) :=
  latitudeMap_norm_sq (by omega) w hw _ (latitudeFrameAt_orthogonal w hw) hr _
    (latitudeMap_norm_sq hn y hy _ (latitudeFrameAt_orthogonal y hy) ht z hz)

/-- A global geometric modulus for the two genuine latitude coordinates.
The bound is uniform in the center, tangent center, and transverse point. -/
theorem nestedLatitude_dist_le {n : ℕ} (hn : 1 ≤ n)
    (w : Vector (n+2)) (hw : ‖w‖^2=(n+2:ℕ)) (y : Vector (n+1)) (hy : ‖y‖^2=(n+1:ℕ))
    {r r₀ t t₀ : ℝ} (hr : |r| ≤ 1) (hr₀ : |r₀| ≤ 1) (ht : |t| ≤ 1) (ht₀ : |t₀| ≤ 1)
    (z : Vector n) (hz : ‖z‖^2=(n:ℝ)) :
    ‖nestedLatitude w y r t z-nestedLatitude w y r₀ t₀ z‖ ≤
      4*Real.sqrt (n+2:ℕ)*(Real.sqrt |r-r₀|+Real.sqrt |t-t₀|) := by
  have hint := latitudeMap_dist_le hn y hy (latitudeFrameAt y) (latitudeFrameAt_orthogonal y hy) ht ht₀ z hz
  have houter := latitudeMap_dist_le (show 1 ≤ n+1 by omega) w hw (latitudeFrameAt w)
    (latitudeFrameAt_orthogonal w hw) hr hr₀ (latitudeMap y (latitudeFrameAt y) t₀ z)
    (latitudeMap_norm_sq hn y hy _ (latitudeFrameAt_orthogonal y hy) ht₀ z hz)
  let a := Real.sqrt (((n+2:ℕ):ℝ)/((n+1:ℕ):ℝ)*(1-r^2))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hr2 : r^2 ≤ 1 := by nlinarith [abs_le.mp hr]
  have ha2 : a ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    have hd : (0:ℝ)<(n+1:ℕ) := by positivity
    have hratio : ((n+2:ℕ):ℝ)/((n+1:ℕ):ℝ) ≤ 2 := by
      apply (div_le_iff₀ hd).mpr
      push_cast
      linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
    calc
      _ ≤ 2*1 := mul_le_mul hratio (by nlinarith [sq_nonneg r]) (by linarith) (by norm_num)
      _ ≤ _ := by norm_num
  have he : nestedLatitude w y r t z-nestedLatitude w y r t₀ z=
      a • latitudeFrameAt w (latitudeMap y (latitudeFrameAt y) t z-latitudeMap y (latitudeFrameAt y) t₀ z) := by
    simp only [nestedLatitude,latitudeMap,map_sub,smul_sub,a]
    abel
  have hinner : ‖nestedLatitude w y r t z-nestedLatitude w y r t₀ z‖ ≤
      4*Real.sqrt (n+2:ℕ)*Real.sqrt |t-t₀| := by
    rw [he,norm_smul,Real.norm_of_nonneg ha,(latitudeFrameAt w).norm_map]
    calc
      _ ≤ 2*(2*Real.sqrt (n+1:ℕ)*Real.sqrt |t-t₀|) := by gcongr
      _ ≤ 4*Real.sqrt (n+2:ℕ)*Real.sqrt |t-t₀| := by
        have hsq : Real.sqrt (n+1:ℕ) ≤ Real.sqrt (n+2:ℕ) := Real.sqrt_le_sqrt (by norm_num)
        nlinarith [mul_nonneg (Real.sqrt_nonneg |t-t₀|) (sub_nonneg.mpr hsq)]
  have htri := dist_triangle (nestedLatitude w y r t z) (nestedLatitude w y r t₀ z)
    (nestedLatitude w y r₀ t₀ z)
  simp only [dist_eq_norm] at htri
  have houter' : ‖nestedLatitude w y r t₀ z-nestedLatitude w y r₀ t₀ z‖ ≤
      2*Real.sqrt (n+2:ℕ)*Real.sqrt |r-r₀| := houter
  nlinarith [mul_nonneg (Real.sqrt_nonneg (n+2:ℕ)) (Real.sqrt_nonneg |r-r₀|)]

/-- Actual smooth H, rather than a field surrogate, varies by at most O(N)
times the two latitude square-root displacements on its physical sphere. -/
theorem nestedLatitude_field_modulus {n : ℕ} (hn : 1 ≤ n) {H : Vector (n+2) → ℝ}
    (hH : Differentiable ℝ H) {K : ℝ} (hK : 0 ≤ K)
    (hgrad : ∀ x ∈ closedBall 0 (Real.sqrt (n+2:ℕ)),‖fderiv ℝ H x‖ ≤ K*Real.sqrt (n+2:ℕ))
    (w : Vector (n+2)) (hw : ‖w‖^2=(n+2:ℕ)) (y : Vector (n+1)) (hy : ‖y‖^2=(n+1:ℕ))
    {r r₀ t t₀ : ℝ} (hr : |r| ≤ 1) (hr₀ : |r₀| ≤ 1) (ht : |t| ≤ 1) (ht₀ : |t₀| ≤ 1)
    (z : Vector n) (hz : ‖z‖^2=(n:ℝ)) :
    |H (nestedLatitude w y r t z)-H (nestedLatitude w y r₀ t₀ z)| ≤
      4*K*(n+2:ℕ)*(Real.sqrt |r-r₀|+Real.sqrt |t-t₀|) := by
  have hball {r t : ℝ} (hr : |r| ≤ 1) (ht : |t| ≤ 1) :
      nestedLatitude w y r t z ∈ closedBall 0 (Real.sqrt (n+2:ℕ)) := by
    rw [mem_closedBall,dist_zero_right,← nestedLatitude_norm_sq hn w hw y hy hr ht z hz,
      Real.sqrt_sq (norm_nonneg _)]
  have hh := (convex_closedBall (0 : Vector (n+2)) (Real.sqrt (n+2:ℕ))).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hH x) hgrad (hball hr₀ ht₀) (hball hr ht)
  have hdist := nestedLatitude_dist_le hn w hw y hy hr hr₀ ht ht₀ z hz
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hdist (mul_nonneg hK (Real.sqrt_nonneg _)))
  apply hh'.trans_eq
  rw [show K*Real.sqrt (n+2:ℕ)*(4*Real.sqrt (n+2:ℕ)*(Real.sqrt |r-r₀|+Real.sqrt |t-t₀|))=
    4*K*(Real.sqrt (n+2:ℕ))^2*(Real.sqrt |r-r₀|+Real.sqrt |t-t₀|) by ring,
    Real.sq_sqrt (Nat.cast_nonneg _)]

end SlowEquilibration.SphericalNestedLatitude
