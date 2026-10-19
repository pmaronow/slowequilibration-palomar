module

public import SphericalAging.SecondVariationSourceError
public import SphericalAging.LpMultiplierTruncation

public section
/-! Bounded actual Jacobian coefficients act continuously on every fixed
predictable L² direction. The proof uses genuine multiplier truncation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowCoefficientApplicationContinuity
open HardSphereDynamics LocalSDE PredictableLinearCoefficient SecondVariationSourceError
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem apply_row_continuous (D : BrownianDriver N P F) {Kb Ks K L : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (Q : PredictableStateL2 N F P) : Continuous (fun y => apply (row D hb hs T g hg hK y) Q) := by
  rw [continuous_iff_continuousAt]
  intro x
  let μ := nonnegativeLebesgueMeasure.prod P
  let a := fun y => row D hb hs T g hg hK y
  let f := fun y => ((GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T : PredictableStateL2 N F P) : Lp (State N) 2 μ)
  let R := fun y => apply (a y) Q-apply (a x) Q
  have hsmall (y : State N) : ∀ᵐ q ∂μ,
      ‖(R y : TimeProcessL2 P) q‖≤(L : ℝ)*‖f y q‖*‖(Q : Lp (State N) 2 μ) q‖ := by
    filter_upwards [Lp.coeFn_sub (apply (a y) Q : TimeProcessL2 P) (apply (a x) Q),
      apply_coeFn (a y) Q,apply_coeFn (a x) Q,
      GlobalSDE.horizonProcess_timeCut D hb hs x T,GlobalSDE.horizonProcess_timeCut D hb hs y T,
      Lp.coeFn_sub (GlobalSDE.horizonClass D hb hs y T : Lp (State N) 2 μ) (GlobalSDE.horizonClass D hb hs x T)]
      with q hr hy hx hX hY hf
    change ‖((apply (a y) Q : TimeProcessL2 P)-(apply (a x) Q : TimeProcessL2 P)) q‖≤_
    rw [hr,Pi.sub_apply,hy,hx]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
    · simp only [a,row,VariationalCoefficients.derivativeRow,ht,ite_true]
      simp only [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] at hX hY
      have hd : ‖fderiv ℝ g (GlobalSDE.horizonProcess D hb hs y T q.1 q.2)-
          fderiv ℝ g (GlobalSDE.horizonProcess D hb hs x T q.1 q.2)‖≤(L : ℝ)*‖f y q‖ := by
        change _≤(L : ℝ)*‖((GlobalSDE.horizonClass D hb hs y T : Lp (State N) 2 μ)-
          (GlobalSDE.horizonClass D hb hs x T : Lp (State N) 2 μ)) q‖
        rw [hf,Pi.sub_apply,←hX,←hY]
        simpa only [dist_eq_norm] using hL.dist_le_mul
          (GlobalSDE.horizonProcess D hb hs y T q.1 q.2) (GlobalSDE.horizonProcess D hb hs x T q.1 q.2)
      rw [←ContinuousLinearMap.sub_apply]
      exact ((fderiv ℝ g (GlobalSDE.horizonProcess D hb hs y T q.1 q.2)-
        fderiv ℝ g (GlobalSDE.horizonProcess D hb hs x T q.1 q.2)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
    · simp only [a,row,VariationalCoefficients.derivativeRow,ht,ite_false,ContinuousLinearMap.zero_apply,sub_self,norm_zero]
      positivity
  have hbounded (y : State N) : ∀ᵐ q ∂μ,
      ‖(R y : TimeProcessL2 P) q‖≤(2*(K : ℝ))*‖(Q : Lp (State N) 2 μ) q‖ := by
    filter_upwards [Lp.coeFn_sub (apply (a y) Q : TimeProcessL2 P) (apply (a x) Q),
      apply_coeFn (a y) Q,apply_coeFn (a x) Q,(a y).bound,(a x).bound]
      with q hr hy hx hby hbx
    change ‖((apply (a y) Q : TimeProcessL2 P)-(apply (a x) Q : TimeProcessL2 P)) q‖≤_
    rw [hr,Pi.sub_apply,hy,hx]
    exact (norm_sub_le _ _).trans ((add_le_add ((a y).value q |>.le_of_opNorm_le hby _)
      ((a x).value q |>.le_of_opNorm_le hbx _)).trans_eq (by ring))
  have hfzero : Tendsto (fun y => lpNorm (f y) 2 μ) (𝓝 x) (𝓝 0) := by
    have hc := (PicardDependence.horizonClass_lipschitz_initial D hb hs T).choose_spec.continuous
    have hh := (hc.sub (continuous_const (y := GlobalSDE.horizonClass D hb hs x T))).norm.tendsto x
    have hh' : Tendsto (fun y => ‖f y‖) (𝓝 x) (𝓝 0) := by
      simpa only [f,Submodule.norm_coe,ClosedSubmodule.norm_coe,Pi.sub_apply,sub_self,norm_zero] using hh
    simpa only [Lp.norm_def,lpNorm] using hh'
  have hz := LpMultiplierTruncation.lpNorm_two_tendsto_zero
    (Lp.memLp (Q : Lp (State N) 2 μ)) L.coe_nonneg (by positivity : 0≤2*(K : ℝ))
    (Filter.Eventually.of_forall (fun y => Lp.memLp (f y)))
    (Filter.Eventually.of_forall (fun y => Lp.aestronglyMeasurable (R y : TimeProcessL2 P)))
    (Filter.Eventually.of_forall hsmall) (Filter.Eventually.of_forall hbounded) hfzero
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  change Tendsto (fun y => ‖(R y : TimeProcessL2 P)‖) (𝓝 x) (𝓝 0)
  simpa only [Lp.norm_def,lpNorm] using hz
end SphericalAging.FlowCoefficientApplicationContinuity
