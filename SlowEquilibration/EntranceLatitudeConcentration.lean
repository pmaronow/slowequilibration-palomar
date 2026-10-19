-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeGaussianRadiusMGF
public import SlowEquilibration.SphericalLatitude

/-! Concentration of actual observables under the manuscript's original
latitude law. The n-dimensional tangent frame and its affine map are the
previously proved geometric constructions, rather than an assumed law
identification. Constants are uniform in the latitude q and dimension n. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceLatitudeConcentration
open MeasureTheory ProbabilityTheory Set
open SphericalModel EntranceLatitudeGaussianRadius
open scoped NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The exact distance multiplier of the genuine affine latitude map. -/
theorem latitudeMap_dist {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (x y : Vector n) :
    dist (latitudeMap u e q x) (latitudeMap u e q y) =
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2)) * dist x y := by
  rw [dist_eq_norm]
  simp only [latitudeMap, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub,
    norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), e.norm_map, dist_eq_norm]

/-- The genuine latitude distance multiplier is uniformly bounded by two;
the squared multiplier is in fact at most two. -/
theorem latitudeMap_scale_le_two {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : |q| ≤ 1) :
    Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2)) ≤ 2 := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : 0 ≤ 1 - q ^ 2 := by nlinarith [abs_le.mp hq]
  have hq1 : 1 - q ^ 2 ≤ 1 := by nlinarith [sq_nonneg q]
  have hratio : ((n+1 : ℕ) : ℝ)/(n : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hnr).mpr
    push_cast
    linarith
  have harg := mul_le_mul hratio hq1 hq0 (by norm_num : (0 : ℝ) ≤ 2)
  have harg0 : 0 ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnr.le) hq0
  have hs := Real.sq_sqrt harg0
  nlinarith [Real.sqrt_nonneg (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2))]

/-- A dimension-uniform actual Lipschitz bound for every admissible latitude. -/
theorem latitudeMap_lipschitz {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) {q : ℝ} (hq : |q| ≤ 1) :
    LipschitzWith 2 (latitudeMap u e q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [latitudeMap_dist]
  exact mul_le_mul_of_nonneg_right (latitudeMap_scale_le_two hn hq) dist_nonneg

/-- The actual images of the tangent sphere lie in the literal latitude slice. -/
theorem latitudeMap_mem_slice {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u = 0) {q : ℝ} (hq : |q| ≤ 1)
    (x : Vector n) (hx : ‖x‖ = Real.sqrt (n : ℝ)) :
    ‖latitudeMap u e q x‖^2=((n+1 : ℕ) : ℝ) ∧ overlap (latitudeMap u e q x) u=q := by
  exact ⟨latitudeMap_norm_sq hn u hu e he hq x (by rw [hx, Real.sq_sqrt (Nat.cast_nonneg n)]),
    overlap_latitude_center u hu e he q x⟩

/-- Pullback of a true Lipschitz observable on the literal latitude slice. -/
theorem latitude_observable_lipschitz_pullback {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u = 0)
    {q : ℝ} (hq : |q| ≤ 1) (f : Vector (n+1) → ℝ) (L : ℝ≥0)
    (hf : LipschitzOnWith L f {v | ‖v‖^2=((n+1 : ℕ) : ℝ) ∧ overlap v u=q}) :
    LipschitzOnWith (2 * L) (f ∘ latitudeMap u e q)
      {x | ‖x‖ = Real.sqrt (n : ℝ)} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hb := hf.dist_le_mul (latitudeMap u e q x) (latitudeMap_mem_slice hn u hu e he hq x hx)
    (latitudeMap u e q y) (latitudeMap_mem_slice hn u hu e he hq y hy)
  have hm := (latitudeMap_lipschitz hn u e hq).dist_le_mul x y
  apply hb.trans
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left hm L.coe_nonneg

/-- An actual centered MGF bound for every bounded Lipschitz observable under
the original manuscript latitude law. The tangent dimension is exactly n,
whereas the physical sphere has squared radius n+1. -/
theorem latitude_observable_centered_mgf_le {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u = 0)
    {q : ℝ} (hq : |q| ≤ 1) (f : Vector (n+1) → ℝ) (hfm : Measurable f) (L : ℝ≥0)
    (hf : LipschitzOnWith L f {v | ‖v‖^2=((n+1 : ℕ) : ℝ) ∧ overlap v u=q})
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ v, ‖v‖^2=((n+1 : ℕ) : ℝ) → overlap v u=q → |f v| ≤ B) (t : ℝ) :
    mgf (fun v => f v - ∫ z, f z ∂latitudeLaw u e q) (latitudeLaw u e q) t ≤
      Real.exp (|t| * ((2 * B) * Real.exp (-(n : ℝ) / 8)) + 32 * (L : ℝ)^2 * t^2) +
        Real.exp (2 * B * |t| - (n : ℝ) / 8) := by
  let F := f ∘ latitudeMap u e q
  have hF : Measurable F := hfm.comp (latitudeMap_continuous u e q).measurable
  have hFL := latitude_observable_lipschitz_pullback hn u hu e he hq f L hf
  have hFb : ∀ x, ‖x‖ = Real.sqrt (n : ℝ) → |F x| ≤ B := by
    intro x hx
    have hv := latitudeMap_mem_slice hn u hu e he hq x hx
    exact hbound _ hv.1 hv.2
  have hmean : (∫ v, f v ∂latitudeLaw u e q) = ∫ x, F x ∂sphereLaw n := by
    rw [latitudeLaw, integral_map (latitudeMap_continuous u e q).measurable.aemeasurable hfm.aestronglyMeasurable]
    rfl
  have hmgf : mgf (fun v => f v - ∫ z, f z ∂latitudeLaw u e q) (latitudeLaw u e q) t =
      mgf (fun x => F x - ∫ y, F y ∂sphereLaw n) (sphereLaw n) t := by
    unfold mgf
    rw [latitudeLaw, integral_map (latitudeMap_continuous u e q).measurable.aemeasurable (by fun_prop),
      ← latitudeLaw, hmean]
    rfl
  have ht := sphere_observable_centered_mgf_le (by omega : 0 < n) F hF (2 * L) hFL hB hFb t
  rw [hmgf]
  have hvariance : 8 * ((2 * L : ℝ≥0) : ℝ)^2 * t^2 = 32 * (L : ℝ)^2 * t^2 := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    ring
  simpa only [hvariance] using ht

end SlowEquilibration.EntranceLatitudeConcentration
