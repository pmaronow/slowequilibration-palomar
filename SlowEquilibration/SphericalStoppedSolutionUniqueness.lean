-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalStoppedSolutionEquation
public import SphericalAging.VectorZeroUniqueness

/-! Local pathwise uniqueness for two actual matrix-Itô strong solutions
whose different drifts obey a Lipschitz comparison up to a stopping time. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalStoppedSolutionUniqueness
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
open SphericalAging
open HardSphereDynamics LocalSDE VectorIto ClosedHitStopping StoppedSDE StoppedVectorIto
open PredictableDriftTime VectorZeroUniqueness
open StaticSDEOperators
open SlowEquilibration.SphericalStoppedSolutionEquation
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem localStrongSolutions_unique_upTo_stop
    (D : BrownianDriver N P F)
    (b c : Fin N → State N → ℝ) (sigma : Fin N → Fin N → State N → ℝ)
    (hb : ∀ i, Continuous (b i)) (hc : ∀ i, Continuous (c i))
    (hsigma : ∀ i j, Continuous (sigma i j))
    (x : State N) (X Y : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hX : IsLocalStrongSolutionOn b sigma hsigma D x X T)
    (hY : IsLocalStrongSolutionOn c sigma hsigma D x Y T)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (L M K : ℝ≥0)
    (hXb : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ L)
    (hYb : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖Y t ω‖ ≤ L)
    (hDrift : ∀ᵐ ω ∂P, ∀ t, t ≤ τ ω → ∀ i,
      ‖b i (X t ω) - c i (Y t ω)‖ ≤ (M : ℝ) * ‖X t ω - Y t ω‖)
    (hNoise : ∀ i j, LipschitzWith K (sigma i j)) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → stoppedState X τ t ω = stoppedState Y τ t ω := by
  obtain ⟨AX,UX,hAX,hUX,hXe⟩ := localStrongSolution_stopped_equation
    D b sigma hb hsigma x X T hXc hX τ hτ hτT
  obtain ⟨AY,UY,hAY,hUY,hYe⟩ := localStrongSolution_stopped_equation
    D c sigma hc hsigma x Y T hYc hY τ hτ hτT
  let Z : ℝ≥0 → Ω → State N := fun t ω => stoppedState X τ t ω - stoppedState Y τ t ω
  let A (i : Fin N) : PredictableProcessL2 F P := AX i - AY i
  let U (i j : Fin N) : PredictableProcessL2 F P := UX i j - UY i j
  have hZa : StronglyAdapted F Z := by
    intro t
    exact (stoppedState_stronglyAdapted X hX.choose hXc hτ t).sub
      (stoppedState_stronglyAdapted Y hY.choose hYc hτ t)
  have hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) := .of_forall fun ω =>
    (stoppedState_continuous X hXc τ ω).sub
      (stoppedState_continuous Y hYc τ ω)
  have hZb : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L+L := by
    filter_upwards [hXb,hYb] with ω hx hy
    intro t
    have ht : min t (τ ω) ≤ T := (min_le_right _ _).trans (hτT ω)
    exact (norm_sub_le _ _).trans (add_le_add (hx _ ht) (hy _ ht))
  have hDriftProd := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hDrift
  have hA (i : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1 ∈ Ioc 0 T → ‖(A i : TimeProcessL2 P) q‖ ≤
        (M : ℝ) * ‖Z q.1 q.2‖ := by
    filter_upwards [Lp.coeFn_sub (AX i : TimeProcessL2 P) (AY i : TimeProcessL2 P),
      hAX i,hAY i,hDriftProd] with q hsub hax hay hcomp
    intro hq
    change ((AX i - AY i : PredictableProcessL2 F P) : TimeProcessL2 P) q =
      (AX i : TimeProcessL2 P) q - (AY i : TimeProcessL2 P) q at hsub
    rw [hsub,hax,hay]
    by_cases hstop : q.1 ≤ τ q.2
    · have hcoef : stoppedTimeCoefficient τ T q = 1 := by
        simp [stoppedTimeCoefficient,hq,hstop]
      simp only [hcoef,one_mul]
      have hZeq : Z q.1 q.2 = X q.1 q.2 - Y q.1 q.2 := by
        simp [Z,stoppedState,min_eq_left hstop]
      rw [hZeq]
      exact hcomp q.1 hstop i
    · have hcoef : stoppedTimeCoefficient τ T q = 0 := by
        simp [stoppedTimeCoefficient,hstop]
      simp only [hcoef,zero_mul,sub_self,norm_zero]
      exact mul_nonneg M.coe_nonneg (norm_nonneg _)
  have hU (i j : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1 ∈ Ioc 0 T → ‖(U i j : TimeProcessL2 P) q‖ ≤
        (K : ℝ) * ‖Z q.1 q.2‖ := by
    filter_upwards [Lp.coeFn_sub (UX i j : TimeProcessL2 P) (UY i j : TimeProcessL2 P),
      hUX i j,hUY i j] with q hsub hux huy
    intro hq
    change ((UX i j - UY i j : PredictableProcessL2 F P) : TimeProcessL2 P) q =
      (UX i j : TimeProcessL2 P) q - (UY i j : TimeProcessL2 P) q at hsub
    rw [hsub,hux,huy]
    by_cases hstop : q.1 ≤ τ q.2
    · have hcoef : stoppedTimeCoefficient τ T q = 1 := by
        simp [stoppedTimeCoefficient,hq,hstop]
      simp only [hcoef,one_mul]
      have hZeq : Z q.1 q.2 = X q.1 q.2 - Y q.1 q.2 := by
        simp [Z,stoppedState,min_eq_left hstop]
      rw [hZeq]
      exact (hNoise i j).norm_sub_le _ _
    · have hcoef : stoppedTimeCoefficient τ T q = 0 := by
        simp [stoppedTimeCoefficient,hstop]
      simp only [hcoef,zero_mul,sub_self,norm_zero]
      exact mul_nonneg K.coe_nonneg (norm_nonneg _)
  have hEq (t : ℝ≥0) (ht : t ≤ T) (i : Fin N) :
      ∀ᵐ ω ∂P, Z t ω i = driftVersion (A i) t t ω +
        (vectorProcessLp D (U i) t : Ω → ℝ) ω := by
    have hvec := vectorProcessLp_sub D (UX i) (UY i) t
    filter_upwards [hXe t ht i,hYe t ht i,
      driftVersion_sub_ae (AX i) (AY i) t,
      Lp.coeFn_sub (vectorProcessLp D (UX i) t : Lp ℝ 2 P)
        (vectorProcessLp D (UY i) t : Lp ℝ 2 P)] with ω hx hy hd hlp
    change ((vectorProcessLp D (UX i) t - vectorProcessLp D (UY i) t : Lp ℝ 2 P) : Ω → ℝ) ω =
      (vectorProcessLp D (UX i) t : Ω → ℝ) ω -
        (vectorProcessLp D (UY i) t : Ω → ℝ) ω at hlp
    change (stoppedState X τ t ω - stoppedState Y τ t ω) i = _
    rw [PiLp.sub_apply,hx,hy,hd t]
    rw [hvec]
    rw [hlp]
    ring
  have hZero := bounded_vector_equation_zero D Z hZa hZc (L+L) M K hZb T
    A U hA hU hEq
  filter_upwards [hZero] with ω hω
  intro t ht
  exact sub_eq_zero.mp (hω t ht)

end SlowEquilibration.SphericalStoppedSolutionUniqueness
