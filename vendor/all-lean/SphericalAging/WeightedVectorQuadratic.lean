module

public import SphericalAging.VectorItoFormula

public section

/-! Actual bracket convergence with arbitrary continuous observed weights.
The verified scalar mixed-bracket theorem is used with a cubic whose half
second derivative is the desired weight. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.WeightedVectorQuadratic
open HardSphereDynamics VectorIto VectorItoFormula VectorQuadraticVariation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def cubic : ℝ → ℝ → ℝ := fun _ z => z^3/3

lemma half_cubic_second (s z : ℝ) : (1/2 : ℝ)*itoSpaceSecondDerivative cubic s z = z := by
  have hfirst : deriv (fun y : ℝ => y^3/3) = fun y => y^2 := by
    funext y
    have h := (((hasDerivAt_id y).pow 3).div_const 3).deriv
    convert h using 1 <;> norm_num <;> ring
  have hsecond : deriv (fun y : ℝ => y^2) z = 2*z := by
    simpa using ((hasDerivAt_id z).pow 2).deriv
  unfold itoSpaceSecondDerivative cubic
  rw [hfirst,hsecond]
  ring

lemma cubic_second (s z : ℝ) : itoSpaceSecondDerivative cubic s z = 2*z := by
  linarith [half_cubic_second s z]

lemma cubic_second_continuous : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative cubic p.1 p.2) := by
  simp_rw [cubic_second]
  fun_prop

@[expose] def weightedQuadraticSum (H M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n,H (uniformPartitionTime t n k) ω*
    (M (uniformPartitionTime t n (k+1)) ω-M (uniformPartitionTime t n k) ω)^2

/-- The actual full-filtration vector Itô integral has its true weighted
bracket density, for every observed continuous scalar weight. -/
theorem vector_weightedQuadratic_tendsto (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) (t : ℝ≥0) :
    TendstoInMeasure P (fun n => weightedQuadraticSum H (vectorProcess D U) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,(U j : ℝ≥0 × Ω → ℝ) (s,ω)^2) ∂nonnegativeLebesgueMeasure) := by
  by_cases ht : t=0
  · subst t
    have hz : (fun n => weightedQuadraticSum H (vectorProcess D U) 0 (n+1)) =
        fun _ : ℕ => fun _ : Ω => (0 : ℝ) := by
      funext n ω
      simp [weightedQuadraticSum,uniformPartitionTime]
    rw [hz]
    simpa using
      (tendstoInMeasure_of_tendsto_ae (μ := P) (fun _ : ℕ => aestronglyMeasurable_const)
        (.of_forall (fun _ : Ω => tendsto_const_nhds)) :
        TendstoInMeasure P (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) atTop (fun _ => 0))
  have htp : 0<t := lt_of_le_of_ne bot_le (Ne.symm ht)
  have hmod : IsContinuousProcessModification H H P := ⟨fun _ => EventuallyEq.rfl,hHc⟩
  let σ := diffusionMagnitude U
  have hQm (a : ℝ≥0) : AEStronglyMeasurable
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) a,σ s ω^2 ∂nonnegativeLebesgueMeasure) P := by
    have hraw := (vectorProcess_beforeStop_diffusionMagnitude D U a a).aestronglyMeasurable
      (fun n => aestronglyMeasurable_quadraticVariationBeforeStopApprox
        (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable) a (n+1) a)
    simpa only [min_self,σ] using hraw
  have hG := bracketStep_process_tendstoInMeasure cubic cubic_second_continuous
    H H σ hH hmod t hQm (diffusionMagnitude_integrable_sq U t)
  have hmix := generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop cubic cubic_second_continuous
    H (vectorProcess D U) hH (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable)
    t htp (fun a ω => ∫ s in Ioc (0 : ℝ≥0) a,σ s ω^2 ∂nonnegativeLebesgueMeasure)
    (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*(σ s ω)^2 ∂nonnegativeLebesgueMeasure)
    (fun a ha => by simpa only [min_eq_right ha,σ] using vectorProcess_beforeStop_diffusionMagnitude D U t a)
    (by simpa only [half_cubic_second] using hG) H hmod
  have he : (fun n => generalItoMixedQuadraticApprox cubic H (vectorProcess D U) t (n+1)) =
      fun n => weightedQuadraticSum H (vectorProcess D U) t (n+1) := by
    funext n ω
    unfold generalItoMixedQuadraticApprox weightedQuadraticSum
    simp only [half_cubic_second]
  rw [he] at hmix
  simpa only [σ,diffusionMagnitude_sq] using hmix

end SphericalAging.WeightedVectorQuadratic
