module

public import SphericalAging.FlowTerminalMomentBounds
public import SphericalAging.LpClassMomentAlgebra
public import SphericalAging.LpEightInterpolationLittleO

public section
/-! True terminal fourth-norm Lipschitz increments and fourth-norm
Fréchet linearization, proved from actual terminal moment receipts. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology Asymptotics
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalLpSpatialBounds
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalMomentBounds LpClassMomentAlgebra
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (x : State N) (T t : ℝ≥0) (hT : 0<T) (ht : t≤T)
include hbg hsg hT ht

theorem increment_terminal_lpNorm_four_le (y : State N) :
    lpNorm (stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
      Lp (State N) 2 P) 4 P≤fourthConstant N Kb Ks T^((1 : ℝ)/4)*‖y-x‖ := by
  have hm := increment_terminal_fourthMoment D₀ hbg hsg hb hs x y T t hT ht
  exact LpMomentBounds.lpNorm_four_le_of_moment hm.1 (fourthConstant_nonneg N Kb Ks T) hm.2

@[expose] def remainder (y : State N) : Lp (State N) 2 P :=
  stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t-
    stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t (y-x)

theorem remainder_memLp_eight (y : State N) : MemLp (remainder D₀ hbg hsg hb hs x T t y) 8 P := by
  exact memLp_sub_coe _ _ (increment_terminal_eighthMoment D₀ hbg hsg hb hs x y T t hT ht).1
    (response_terminal_eighthMoment (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x (y-x) T t ht).1

theorem remainder_lpNorm_eight_le (y : State N) :
    lpNorm (remainder D₀ hbg hsg hb hs x T t y) 8 P≤2*eighthConstant N Kb Ks T^((1 : ℝ)/8)*‖y-x‖ := by
  have hi := increment_terminal_eighthMoment D₀ hbg hsg hb hs x y T t hT ht
  have hv := response_terminal_eighthMoment (NullAugmentation.driver D₀) hbg hsg hb hs
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x (y-x) T t ht
  have hni := LpMomentBounds.lpNorm_eight_le_of_moment hi.1 (eighthConstant_nonneg N Kb Ks T) hi.2
  have hnv := LpMomentBounds.lpNorm_eight_le_of_moment hv.1 (eighthConstant_nonneg N Kb Ks T) hv.2
  exact (lpNorm_sub_coe_le _ _ hi.1 (by norm_num)).trans (by linarith)

theorem remainder_lpNorm_four_isLittleO {Lb Ls : ℝ≥0}
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j))) :
    (fun y => lpNorm (remainder D₀ hbg hsg hb hs x T t y) 4 P)=o[𝓝 x] (fun y => y-x) := by
  have hderiv := stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT
  have hsmall : (fun y => lpNorm (remainder D₀ hbg hsg hb hs x T t y) 2 P)=o[𝓝 x] (fun y => y-x) := by
    simpa only [lpNorm_two_coe,remainder] using hderiv.isLittleO.norm_left
  have hbound : (fun y => lpNorm (remainder D₀ hbg hsg hb hs x T t y) 8 P)=O[𝓝 x] (fun y => y-x) := by
    apply IsBigO.of_bound
    refine .of_forall (fun y => ?_)
    rw [Real.norm_of_nonneg lpNorm_nonneg]
    exact remainder_lpNorm_eight_le D₀ hbg hsg hb hs x T t hT ht y
  exact LpEightInterpolationLittleO.lpNorm_four_isLittleO
    (.of_forall (fun y => Lp.memLp _))
    (.of_forall (remainder_memLp_eight D₀ hbg hsg hb hs x T t hT ht)) hsmall hbound
end Flow
end SphericalAging.FlowTerminalLpSpatialBounds
