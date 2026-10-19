module

public import SphericalAging.HamiltonianVariational
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-! Actual secant derivative rows and Taylor bounds used to identify the
stochastic variational equation with nonlinear solution difference quotients. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecantCoefficient
set_option maxHeartbeats 1200000
open HardSphereDynamics LocalSDE VariationalCoefficients
variable {N p : ℕ}

/-- The genuine averaged Fréchet derivative along the straight segment. -/
@[expose] def secantRow (g : State N → ℝ) (x y : State N) : State N →L[ℝ] ℝ :=
  ∫ r in (0 : ℝ)..1, fderiv ℝ g (x + r • (y-x))

theorem secant_integrand_continuous {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (x y : State N) :
    Continuous (fun r : ℝ => fderiv ℝ g (x+r•(y-x))) :=
  (hg.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))

theorem secantRow_bound {g : State N → ℝ} {K : ℝ≥0} (hL : LipschitzWith K g) (x y : State N) :
    ‖secantRow g x y‖ ≤ K := by
  unfold secantRow
  simpa only [sub_zero,abs_one,one_mul,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun r _ => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := x+r•(y-x)))

theorem secantRow_continuous {g : State N → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : ℝ≥0} (hL : LipschitzWith K g) : Continuous (fun z : State N × State N => secantRow g z.1 z.2) := by
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ : ℝ => (K : ℝ))
  · intro z
    exact (secant_integrand_continuous hg z.1 z.2).aestronglyMeasurable
  · exact fun z => .of_forall (fun r _ => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := z.1+r•(z.2-z.1)))
  · exact intervalIntegrable_const
  · exact .of_forall (fun r _ => (hg.continuous_fderiv (by simp)).comp
      (continuous_fst.add ((continuous_snd.sub continuous_fst).const_smul r)))

/-- Exact fundamental theorem of calculus: the actual coefficient increment
is the averaged derivative acting on the actual state increment. -/
theorem secantRow_increment {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (x y : State N) :
    secantRow g x y (y-x) = g y-g x := by
  have hi := (secant_integrand_continuous hg x y).intervalIntegrable (μ := volume) 0 1
  rw [secantRow,ContinuousLinearMap.intervalIntegral_apply hi]
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => g (x+r•(y-x)))
      (fderiv ℝ g (x+r•(y-x)) (y-x)) r :=
    ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt r
      (by
        convert (hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const (y-x)) using 1
        · funext s
          rfl
        · simp)
  have hj : IntervalIntegrable (fun r : ℝ => fderiv ℝ g (x+r•(y-x)) (y-x)) volume 0 1 :=
    ((secant_integrand_continuous hg x y).clm_apply continuous_const).intervalIntegrable _ _
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hj

/-- True quadratic Taylor remainder under a genuine global derivative
Lipschitz bound. -/
theorem taylor_remainder_bound {g : State N → ℝ} (hg : ContDiff ℝ ∞ g)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ g)) (x y : State N) :
    ‖g y-g x-fderiv ℝ g x (y-x)‖ ≤ (L : ℝ) * ‖y-x‖^2 := by
  let f : State N → ℝ := fun z => g z-g x-fderiv ℝ g x (z-x)
  have hd (z : State N) : HasFDerivAt f (fderiv ℝ g z-fderiv ℝ g x) z := by
    exact (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).sub_const _).sub
      ((fderiv ℝ g x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hb : ∀ z ∈ Metric.closedBall x ‖y-x‖, ‖fderiv ℝ f z‖ ≤ (L : ℝ)*‖y-x‖ := by
    intro z hz
    rw [(hd z).fderiv]
    exact (hL.norm_sub_le z x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) L.coe_nonneg)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hd z).differentiableAt) hb
    (convex_closedBall x ‖y-x‖) (Metric.mem_closedBall_self (norm_nonneg (y-x)))
    (show y ∈ Metric.closedBall x ‖y-x‖ from by simp [Metric.mem_closedBall,dist_eq_norm])
  simpa only [f,sub_self,map_zero,sub_zero,mul_assoc,← pow_two] using hh



theorem cutoffDrift_derivative_lipschitz (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (i : Fin N) :
    ∃ L : ℝ≥0, LipschitzWith L (fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)) := by
  have hg := cutoffDrift_contDiff β J R hR i
  have hs : HasCompactSupport (CutoffSDE.cutoffDrift β J R hR i) :=
    (cutoffCoefficient_hasCompactSupport R hR (hamiltonianDrift β J)).comp_left (g := fun x : State N => x i) (by rfl)
  exact ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv (𝕜 := ℝ))
    (hg.fderiv_right (m := ∞) (by simp)) (by simp)

theorem cutoffNoise_derivative_lipschitz (R : ℝ) (hR : 0 < R) (i j : Fin N) :
    ∃ L : ℝ≥0, LipschitzWith L (fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)) := by
  have hg := cutoffNoise_contDiff R hR i j
  have hs : HasCompactSupport (CutoffSDE.cutoffNoise N R hR i j) :=
    (cutoffCoefficient_hasCompactSupport R hR (fun x : State N => noiseColumn x j)).comp_left (g := fun x : State N => x i) (by rfl)
  exact ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv (𝕜 := ℝ))
    (hg.fderiv_right (m := ∞) (by simp)) (by simp)

end SphericalAging.SecantCoefficient
