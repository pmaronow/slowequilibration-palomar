module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

public section

/-! Actual smooth approximations of a finite-dimensional Lipschitz
observable preserve its Lipschitz constant. This removes differentiability
from Gaussian concentration without a smooth-approximation premise. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.LipschitzBumpApproximation
open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology Convolution NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[expose] def mollify (μ : Measure E) (φ : ContDiffBump (0 : E)) (f : E→ℝ) : E→ℝ :=
  φ.normed μ ⋆[lsmul ℝ ℝ,μ] f

theorem mollify_contDiff (μ : Measure E) [μ.IsAddHaarMeasure]
    (φ : ContDiffBump (0 : E)) (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify μ φ f) :=
  (φ.hasCompactSupport_normed (μ:=μ)).contDiff_convolution_left (n:=(⊤ : ℕ∞)) (μ:=μ) (lsmul ℝ ℝ)
    (φ.contDiff_normed (μ:=μ)) hf.continuous.locallyIntegrable

theorem mollify_lipschitz (μ : Measure E) [μ.IsAddHaarMeasure]
    (φ : ContDiffBump (0 : E)) (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (mollify μ φ f) := by
  have hex := (φ.hasCompactSupport_normed (μ:=μ)).convolutionExists_left_of_continuous_right (μ:=μ) (lsmul ℝ ℝ)
    (φ.integrable_normed (μ:=μ)).locallyIntegrable hf.continuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,mollify,convolution,convolution,←integral_sub (hex x).integrable (hex y).integrable]
  change |∫t,φ.normed μ t*f (x-t)-φ.normed μ t*f (y-t) ∂μ|≤(L:ℝ)*dist x y
  have hnorm : (fun t => ‖φ.normed μ t*f (x-t)-φ.normed μ t*f (y-t)‖)=
      (fun t => φ.normed μ t*|f (x-t)-f (y-t)|) := by
    funext t
    rw [Real.norm_eq_abs,←mul_sub,abs_mul,abs_of_nonneg (φ.nonneg_normed _)]
  have hh := norm_integral_le_integral_norm (μ:=μ) (fun t => φ.normed μ t*f (x-t)-φ.normed μ t*f (y-t))
  rw [hnorm] at hh
  have hnormI := ((hex x).integrable.sub (hex y).integrable).norm
  change Integrable (fun t => ‖φ.normed μ t*f (x-t)-φ.normed μ t*f (y-t)‖) μ at hnormI
  rw [hnorm] at hnormI
  have hdomI := (φ.integrable_normed (μ:=μ)).mul_const ((L:ℝ)*dist x y)
  have hi := integral_mono hnormI hdomI (fun t => by
    have ht := hf.dist_le_mul (x-t) (y-t)
    rw [Real.dist_eq,dist_sub_right] at ht
    exact mul_le_mul_of_nonneg_left ht (φ.nonneg_normed t))
  have hdom : (∫t,φ.normed μ t*((L:ℝ)*dist x y) ∂μ)=(L:ℝ)*dist x y := by
    rw [integral_mul_const,φ.integral_normed,one_mul]
  exact hh.trans (hi.trans_eq hdom)

theorem mollify_error (μ : Measure E) [μ.IsAddHaarMeasure]
    (φ : ContDiffBump (0 : E)) (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    dist (mollify μ φ f x) (f x)≤(L:ℝ)*φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le L.coe_nonneg)

@[expose] def bump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1/(2*((n:ℝ)+1))
  rOut := 1/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_left zero_lt_one (by positivity)
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    linarith

theorem exists_smooth_lipschitz_approximation (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∃g : ℕ→E→ℝ,
      (∀n,ContDiff ℝ (⊤ : ℕ∞) (g n)) ∧ (∀n,LipschitzWith L (g n)) ∧
      (∀n x,dist (g n x) (f x)≤(L:ℝ)/((n:ℝ)+1)) ∧
      (∀x,Tendsto (fun n => g n x) atTop (𝓝 (f x))) ∧
      (∀n x,‖fderiv ℝ (g n) x‖≤L) := by
  refine ⟨fun n => mollify μ (bump n) f,
    fun n => mollify_contDiff μ (bump n) f hf,
    fun n => mollify_lipschitz μ (bump n) f hf,?_,?_,?_⟩
  · intro n x
    simpa only [bump,div_eq_mul_inv,one_mul] using mollify_error μ (bump n) f hf x
  · intro x
    exact ContDiffBump.convolution_tendsto_right_of_continuous
      (by simpa only [bump] using tendsto_one_div_add_atTop_nhds_zero_nat) hf.continuous x
  · intro n x
    exact norm_fderiv_le_of_lipschitz ℝ (mollify_lipschitz μ (bump n) f hf)

end SphericalAging.LipschitzBumpApproximation
