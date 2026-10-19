module

public import SphericalAging.HardSphereStochastic
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

public section

/-! Finite Euclidean laws supported on the physical sphere are determined
by compact C² scalar tests. The continuous compact tests are approximated
by genuine smooth functions and then cut off by the actual coefficient
bump, so no test-density premise is supplied. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff CompactlySupported
namespace SphericalAging.SphereSmoothTestMeasureExt
open HardSphereDynamics
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/-- A fixed actual smooth coefficient cutoff is one on the physical sphere. -/
theorem coefficientBump_one_onSphere {x : State N} (hx : OnSphere x) :
    coefficientBump (N := N) ((N : ℝ)+1) (by positivity) x=1 := by
  have hnorm : ‖x‖≤(N : ℝ)+1 := by
    have hh := (onSphere_iff_norm_sq x).mp hx
    nlinarith [norm_nonneg x,Nat.cast_nonneg (α := ℝ) N]
  have hm : x∈Metric.closedBall (0 : State N)
      (coefficientBump (N := N) ((N : ℝ)+1) (by positivity)).rIn := by
    simpa only [coefficientBump,Metric.mem_closedBall,dist_zero_right] using hnorm
  exact (coefficientBump (N := N) ((N : ℝ)+1) (by positivity)).one_of_mem_closedBall hm

/-- Smooth compact approximants uniformly approximate every compact
continuous scalar test on the true sphere. -/
theorem exists_compactC2_sphere_approximation (f : C_c(State N, ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∃ g : State N → ℝ,ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∀ x,OnSphere x→dist (f x) (g x)<ε := by
  obtain ⟨g,hg,hgf⟩ := (CompactlySupportedContinuousMapClass.uniformContinuous f).exists_contDiff_dist_le hε
  let G : State N → ℝ := fun x => coefficientBump (N := N) ((N : ℝ)+1) (by positivity) x*g x
  refine ⟨G,?_,?_,?_⟩
  · exact ((coefficientBump (N := N) ((N : ℝ)+1) (by positivity)).contDiff.mul hg).of_le (by simp)
  · exact (coefficientBump (N := N) ((N : ℝ)+1) (by positivity)).hasCompactSupport.mul_right
  · intro x hx
    simp only [G,coefficientBump_one_onSphere hx,one_mul]
    exact (dist_comm (f x) (g x)).trans_lt (hgf x)

/-- Equality against all compact C² tests determines every finite
sphere-supported Euclidean measure. The test-class approximation and
finite-law integration are conclusions, not assumptions. -/
theorem measure_eq_of_compactC2_integrals {μ ν : Measure (State N)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ,OnSphere x) (hν : ∀ᵐ x ∂ν,OnSphere x)
    (htests : ∀ f : State N → ℝ,ContDiff ℝ 2 f→HasCompactSupport f→
      (∫ x,f x ∂μ)=∫ x,f x ∂ν) : μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  apply eq_of_forall_dist_le
  intro ε hε
  let δ : ℝ := ε/(μ.real univ+ν.real univ+1)
  have hd : 0<μ.real univ+ν.real univ+1 := by positivity
  have hδ : 0<δ := div_pos hε hd
  obtain ⟨g,hg,hgc,hgf⟩ := exists_compactC2_sphere_approximation f hδ
  have hfiμ : Integrable (fun x => f x) μ := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hfiν : Integrable (fun x => f x) ν := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hgiμ : Integrable g μ := hg.continuous.integrable_of_hasCompactSupport hgc
  have hgiν : Integrable g ν := hg.continuous.integrable_of_hasCompactSupport hgc
  have he := htests g hg hgc
  have hdistμ : dist (∫ x,f x ∂μ) (∫ x,g x ∂μ)≤δ*μ.real univ := by
    rw [dist_eq_norm,← integral_sub hfiμ hgiμ]
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hμ] with x hx
    exact (show ‖f x-g x‖<δ from by simpa only [dist_eq_norm] using hgf x hx).le
  have hdistν : dist (∫ x,g x ∂ν) (∫ x,f x ∂ν)≤δ*ν.real univ := by
    rw [dist_comm,dist_eq_norm,← integral_sub hfiν hgiν]
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hν] with x hx
    exact (show ‖f x-g x‖<δ from by simpa only [dist_eq_norm] using hgf x hx).le
  calc
    _≤dist (∫ x,f x ∂μ) (∫ x,g x ∂μ)+dist (∫ x,g x ∂μ) (∫ x,f x ∂ν) := dist_triangle _ _ _
    _=dist (∫ x,f x ∂μ) (∫ x,g x ∂μ)+dist (∫ x,g x ∂ν) (∫ x,f x ∂ν) := by rw [he]
    _≤δ*μ.real univ+δ*ν.real univ := add_le_add hdistμ hdistν
    _≤ε := by
      have heq : δ*(μ.real univ+ν.real univ+1)=ε := by dsimp only [δ];field_simp
      nlinarith

end SphericalAging.SphereSmoothTestMeasureExt
