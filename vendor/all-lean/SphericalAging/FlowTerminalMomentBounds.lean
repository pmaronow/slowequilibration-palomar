module

public import SphericalAging.FlowVariationEighthMoment
public import SphericalAging.FlowTerminalDerivative
public import SphericalAging.LpMomentBounds

public section
/-! Actual fixed-terminal fourth and eighth moments of constructed
initial-state variations and nonlinear increments. These are probability
space receipts, distinct from product-time moment bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalMomentBounds
open HardSphereDynamics LocalSDE FlowTerminalDerivative StochasticDifferenceQuotient
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def fourthConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  Real.exp ((RandomLinearSDETimeFourthMoment.momentRate N Kb Ks : ℝ)*T)
@[expose] def eighthConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  Real.exp ((RandomLinearSDETimeEighthMoment.momentRate N Kb Ks : ℝ)*T)
lemma fourthConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) : 0≤fourthConstant N Kb Ks T := Real.exp_nonneg _
lemma eighthConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) : 0≤eighthConstant N Kb Ks T := Real.exp_nonneg _

theorem linear_solution_terminal_fourthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : LinearVariationalSDE.IsStrongSolutionOn a sigma D v X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) :
    MemLp (X t) 4 P ∧ (∫ omega,‖X t omega‖^4 ∂P)≤fourthConstant N Kb Ks T*‖v‖^4 := by
  have hr : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D (fun _ => v) X T := h
  have hh := RandomLinearSDETimeFourthMoment.linear_solution_fourthMoment hr
    (memLp_const v) ‖v‖₊ (.of_forall (fun _ => le_rfl)) hnull t ht
  refine ⟨hh.1,?_⟩
  simpa only [RandomLinearSDETimeFourthMoment.momentConstant,integral_const,
    probReal_univ,one_smul,fourthConstant,mul_comm] using hh.2

theorem linear_solution_terminal_eighthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : LinearVariationalSDE.IsStrongSolutionOn a sigma D v X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) :
    MemLp (X t) 8 P ∧ (∫ omega,‖X t omega‖^8 ∂P)≤eighthConstant N Kb Ks T*‖v‖^8 := by
  have hr : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D (fun _ => v) X T := h
  have hh := RandomLinearSDETimeEighthMoment.linear_solution_eighthMoment hr
    (memLp_const v) ‖v‖₊ (.of_forall (fun _ => le_rfl)) hnull t ht
  refine ⟨hh.1,?_⟩
  simpa only [RandomLinearSDETimeEighthMoment.momentConstant,integral_const,
    probReal_univ,one_smul,eighthConstant,mul_comm] using hh.2

section Flow
variable (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x v : State N) (T t : ℝ≥0) (ht : t≤T)
include hnull ht

theorem response_terminal_fourthMoment :
    MemLp (stateResponse D hbg hsg hb hs x T t v : Ω → State N) 4 P ∧
      (∫ omega,‖stateResponse D hbg hsg hb hs x T t v omega‖^4 ∂P)≤fourthConstant N Kb Ks T*‖v‖^4 := by
  have hm := linear_solution_terminal_fourthMoment
    (ConstructedFirstVariation.process_strongSolution D hbg hsg hb hs x T v) hnull t ht
  have he := stateResponse_ae D hbg hsg hb hs x v T t
  refine ⟨hm.1.ae_eq he.symm,?_⟩
  exact (integral_congr_ae (he.fun_comp (fun z : State N => ‖z‖^4))).trans_le (by simpa only [Function.comp_apply,ConstructedFirstVariation.process] using hm.2)

theorem response_terminal_eighthMoment :
    MemLp (stateResponse D hbg hsg hb hs x T t v : Ω → State N) 8 P ∧
      (∫ omega,‖stateResponse D hbg hsg hb hs x T t v omega‖^8 ∂P)≤eighthConstant N Kb Ks T*‖v‖^8 := by
  have hm := linear_solution_terminal_eighthMoment
    (ConstructedFirstVariation.process_strongSolution D hbg hsg hb hs x T v) hnull t ht
  have he := stateResponse_ae D hbg hsg hb hs x v T t
  refine ⟨hm.1.ae_eq he.symm,?_⟩
  exact (integral_congr_ae (he.fun_comp (fun z : State N => ‖z‖^8))).trans_le (by simpa only [Function.comp_apply,ConstructedFirstVariation.process] using hm.2)
end Flow

section Increment
variable (D₀ : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (x y : State N) (T t : ℝ≥0) (hT : 0<T) (ht : t≤T)

theorem increment_terminal_ae :
    (stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
      Lp (State N) 2 P)=ᵐ[P] NonlinearIncrementFourthMoment.increment (NullAugmentation.driver D₀) hb hs x y T t := by
  filter_upwards [Lp.coeFn_sub (stateClass (NullAugmentation.driver D₀) hb hs y T t)
    (stateClass (NullAugmentation.driver D₀) hb hs x T t),stateClass_ae (NullAugmentation.driver D₀) hb hs x T t,
    stateClass_ae (NullAugmentation.driver D₀) hb hs y T t] with omega hsub hx hy
  exact hsub.trans (congrArg₂ (fun a b : State N => a-b) hy hx)

include hbg hsg hT ht in
theorem increment_terminal_fourthMoment :
    MemLp (stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
      Lp (State N) 2 P) 4 P ∧
      (∫ omega,‖(stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
        Lp (State N) 2 P) omega‖^4 ∂P)≤fourthConstant N Kb Ks T*‖y-x‖^4 := by
  obtain ⟨Z,hZ,hcommon⟩ := constructed_scaled_difference (NullAugmentation.driver D₀) hbg hsg hb hs x y T hT 1
  have he : (stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
      Lp (State N) 2 P)=ᵐ[P] Z t := by
    have hc : Z t=ᵐ[P] NonlinearIncrementFourthMoment.increment (NullAugmentation.driver D₀) hb hs x y T t := by
      filter_upwards [hcommon] with omega homega
      simpa only [one_smul,NonlinearIncrementFourthMoment.increment] using homega t ht
    exact (increment_terminal_ae D₀ hb hs x y T t).trans hc.symm
  have hm := linear_solution_terminal_fourthMoment hZ
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) t ht
  refine ⟨hm.1.ae_eq he.symm,?_⟩
  exact (integral_congr_ae (he.fun_comp (fun z : State N => ‖z‖^4))).trans_le (by simpa only [one_smul,Function.comp_apply] using hm.2)

include hbg hsg hT ht in
theorem increment_terminal_eighthMoment :
    MemLp (stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
      Lp (State N) 2 P) 8 P ∧
      (∫ omega,‖(stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
        Lp (State N) 2 P) omega‖^8 ∂P)≤eighthConstant N Kb Ks T*‖y-x‖^8 := by
  obtain ⟨Z,hZ,hcommon⟩ := constructed_scaled_difference (NullAugmentation.driver D₀) hbg hsg hb hs x y T hT 1
  have he : (stateClass (NullAugmentation.driver D₀) hb hs y T t-stateClass (NullAugmentation.driver D₀) hb hs x T t :
      Lp (State N) 2 P)=ᵐ[P] Z t := by
    have hc : Z t=ᵐ[P] NonlinearIncrementFourthMoment.increment (NullAugmentation.driver D₀) hb hs x y T t := by
      filter_upwards [hcommon] with omega homega
      simpa only [one_smul,NonlinearIncrementFourthMoment.increment] using homega t ht
    exact (increment_terminal_ae D₀ hb hs x y T t).trans hc.symm
  have hm := linear_solution_terminal_eighthMoment hZ
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) t ht
  refine ⟨hm.1.ae_eq he.symm,?_⟩
  exact (integral_congr_ae (he.fun_comp (fun z : State N => ‖z‖^8))).trans_le (by simpa only [one_smul,Function.comp_apply] using hm.2)
end Increment
end SphericalAging.FlowTerminalMomentBounds
