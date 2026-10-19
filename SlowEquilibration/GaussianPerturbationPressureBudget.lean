-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationResponse

@[expose] public section

/-! # Actual Gaussian perturbation pressure budget

Selected Gaussian coordinates can only increase the true mean log
partition. Their contribution is bounded by half the literal diagonal
feature energy, independently of the spin law and coordinate dimension.
-/
namespace SlowEquilibration.GaussianPerturbationPressureBudget
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationResponse
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem meanScore_mem_Icc_of_nonneg (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν,(∑ i,if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    {x : ℝ} (hx : 0 ≤ x) : meanScore ν L label x ∈ Icc 0 (x*a) := by
  constructor
  · rw [meanScore_response ν L hL hK hb label x]
    apply mul_nonneg hx
    exact integral_nonneg fun w => (varianceTrace_mem_Icc ν L hL hK hb label hdiag x w).1
  · exact (le_abs_self _).trans (by simpa only [abs_of_nonneg hx] using
      (abs_meanScore_le ν L hL hK hb label hdiag x))

/-- The real selected-coordinate amplitude has the true mean pressure
increment in [0,a r²/2]. The bound is proved from Gaussian IBP and actual
Gibbs variances; it is uniform in every other Gaussian field coordinate. -/
theorem parameterMean_increment_mem_Icc (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν,(∑ i,if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    {r : ℝ} (hr : 0 ≤ r) :
    parameterMean ν L label r-parameterMean ν L label 0 ∈ Icc 0 (a*r^2/2) := by
  let P := parameterMean ν L label
  let Q := fun x : ℝ => P x-a*x^2/2
  have hdP (x : ℝ) : HasDerivAt P (meanScore ν L label x) x :=
    parameterMean_hasDerivAt ν L hL hK hb label x
  have hdQ (x : ℝ) : HasDerivAt Q (meanScore ν L label x-a*x) x := by
    convert (hdP x).sub ((((hasDerivAt_id x).pow 2).const_mul a).div_const 2) using 1
    · funext y
      dsimp only [Q,Pi.sub_apply,Pi.pow_apply,id_eq]
    · simp only [id_eq]
      ring
  have hmono : MonotoneOn P (Icc (0 : ℝ) r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun x => (hdP x).continuousAt)).continuousOn
      (fun x _ => (hdP x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hdP x).deriv]
    exact (meanScore_mem_Icc_of_nonneg ν L hL hK hb label hdiag (interior_subset hx).1).1
  have hanti : AntitoneOn Q (Icc (0 : ℝ) r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun x => (hdQ x).continuousAt)).continuousOn
      (fun x _ => (hdQ x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hdQ x).deriv]
    have hh := (meanScore_mem_Icc_of_nonneg ν L hL hK hb label hdiag (interior_subset hx).1).2
    nlinarith
  have hp := hmono ⟨le_rfl,hr⟩ ⟨hr,le_rfl⟩ hr
  have hq := hanti ⟨le_rfl,hr⟩ ⟨hr,le_rfl⟩ hr
  dsimp only [P,Q] at hp hq
  constructor <;> nlinarith

/-- In particular the finite perturbation at its literal amplitude one
costs at most half its actual selected-coordinate diagonal energy. -/
theorem parameterMean_one_sub_zero_mem_Icc (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν,(∑ i,if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a) :
    parameterMean ν L label 1-parameterMean ν L label 0 ∈ Icc 0 (a/2) := by
  simpa only [one_pow,mul_one] using
    parameterMean_increment_mem_Icc ν L hL hK hb label hdiag zero_le_one

end
end SlowEquilibration.GaussianPerturbationPressureBudget
