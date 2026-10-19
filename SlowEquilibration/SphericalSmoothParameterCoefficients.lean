-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalC1Dynamics
public import SlowEquilibration.SphericalDisorderKernelMeasurable
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.Floor

/-! Actual smooth parameter localization of spherical Langevin coefficients.
Compact joint support derives every required Lipschitz constant. -/
@[expose] public section
namespace SlowEquilibration.SphericalSmoothParameter
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalDynamics SphericalC1Dynamics
open SphericalAging HardSphereDynamics
open scoped Topology NNReal ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
variable {N : ℕ} {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [FiniteDimensional ℝ Θ]

def parameterBump (m : ℕ) : ContDiffBump (0 : Θ) :=
  ⟨(m:ℝ)+1,2*((m:ℝ)+1),by positivity,by linarith [show 0 ≤ (m:ℝ) by positivity]⟩

def localizedDriftVector (β : ℝ) (g : Θ×Vector N→Vector N) (m : ℕ)
    (z : Θ×Vector N) : Vector N :=
  parameterBump (Θ:=Θ) m z.1 •
    cutoffCoefficient (cutoffRadius N) (cutoffRadius_pos N) (drift β (fun x=>g (z.1,x))) z.2

omit [FiniteDimensional ℝ Θ] in
theorem jointDrift_contDiff (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun z : Θ×Vector N=>drift β (fun x=>g (z.1,x)) z.2) := by
  have hp : ContDiff ℝ 1 (fun z : Θ×Vector N=>projection z.2 (g z)) := by
    simp only [projection,div_eq_mul_inv]
    exact hg.sub (((contDiff_snd.inner ℝ hg).mul contDiff_const).smul contDiff_snd)
  exact hp.const_smul β |>.sub (contDiff_snd.const_smul (kappa N))

theorem localizedDriftVector_contDiff (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) : ContDiff ℝ 1 (localizedDriftVector β g m) := by
  exact ((parameterBump (Θ:=Θ) m).contDiff.comp contDiff_fst).smul
    (((coefficientBump (N:=N) (cutoffRadius N) (cutoffRadius_pos N)).contDiff.comp contDiff_snd).smul
      (jointDrift_contDiff β g hg))

theorem localizedDriftVector_hasCompactSupport (β : ℝ) (g : Θ×Vector N→Vector N) (m : ℕ) :
    HasCompactSupport (localizedDriftVector β g m) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_closedBall (0:Θ) (parameterBump (Θ:=Θ) m).rOut).prod
      (isCompact_closedBall (0:Vector N) (coefficientBump (N:=N) (cutoffRadius N) (cutoffRadius_pos N)).rOut))
  intro z hz
  have hp : z.1 ∈ support (parameterBump (Θ:=Θ) m) := by
    intro hzero
    exact hz (by simp only [localizedDriftVector,hzero,zero_smul])
  have hx : z.2 ∈ support (coefficientBump (N:=N) (cutoffRadius N) (cutoffRadius_pos N)) := by
    intro hzero
    exact hz (by simp only [localizedDriftVector,cutoffCoefficient,hzero,zero_smul,smul_zero])
  rw [(parameterBump (Θ:=Θ) m).support_eq] at hp
  rw [(coefficientBump (N:=N) (cutoffRadius N) (cutoffRadius_pos N)).support_eq] at hx
  exact ⟨Metric.ball_subset_closedBall hp,Metric.ball_subset_closedBall hx⟩

theorem localizedDriftVector_lipschitz (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) :
    ∃ K : ℝ≥0,LipschitzWith K (localizedDriftVector β g m) :=
  ContDiff.lipschitzWith_of_hasCompactSupport
    (localizedDriftVector_hasCompactSupport β g m) (localizedDriftVector_contDiff β g hg m) (by norm_num)

def localizedDrift (β : ℝ) (g : Θ×Vector N→Vector N) (m : ℕ)
    (θ : Θ) (i : Fin N) (x : Vector N) : ℝ := localizedDriftVector β g m (θ,x) i

theorem localizedDrift_state_lipschitz (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) :
    ∃ K : ℝ≥0,∀ θ i,LipschitzWith K (localizedDrift β g m θ i) := by
  obtain ⟨K,hK⟩ := localizedDriftVector_lipschitz β g hg m
  refine ⟨K,fun θ i=>?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := ((CutoffSDE.coordinate_lipschitz i).comp hK).dist_le_mul (θ,x) (θ,y)
  simpa only [localizedDrift,Function.comp_def,one_mul,Prod.dist_eq,dist_self,
    max_eq_right (show 0 ≤ dist x y from dist_nonneg)] using hh

theorem localizedDrift_parameter_lipschitz (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) :
    ∃ K : ℝ≥0,∀ θ φ i x,‖localizedDrift β g m θ i x-localizedDrift β g m φ i x‖ ≤ K*‖θ-φ‖ := by
  obtain ⟨K,hK⟩ := localizedDriftVector_lipschitz β g hg m
  refine ⟨K,fun θ φ i x=>?_⟩
  have hh := ((CutoffSDE.coordinate_lipschitz i).comp hK).dist_le_mul (θ,x) (φ,x)
  simp only [one_mul,Prod.dist_eq,dist_self,max_eq_left (show 0 ≤ dist θ φ from dist_nonneg)] at hh
  simpa only [localizedDrift,Function.comp_def,dist_eq_norm] using hh

theorem localizedDrift_eq (β : ℝ) (g : Θ×Vector N→Vector N) (m : ℕ)
    (θ : Θ) (hθ : ‖θ‖ ≤ (m:ℝ)+1) :
    localizedDrift β g m θ = cutoffDrift β (fun x=>g (θ,x)) (cutoffRadius N) (cutoffRadius_pos N) := by
  have hm : θ ∈ Metric.closedBall (0:Θ) (parameterBump (Θ:=Θ) m).rIn := by
    simpa only [Metric.mem_closedBall,dist_zero_right,parameterBump] using hθ
  funext i x
  simp only [localizedDrift,localizedDriftVector,(parameterBump (Θ:=Θ) m).one_of_mem_closedBall hm,one_smul,cutoffDrift]

def parameterIndex (θ : Θ) : ℕ := Nat.ceil ‖θ‖

omit [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ] in
theorem parameterIndex_bound (θ : Θ) : ‖θ‖ ≤ (parameterIndex θ:ℝ)+1 := by
  exact (Nat.le_ceil ‖θ‖).trans (le_add_of_nonneg_right (by norm_num))

end
end SlowEquilibration.SphericalSmoothParameter
