module

public import SphericalAging.ActualSphereFeller
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

public section

/-! Literal Chapman–Kolmogorov equality of the actual sphere SDE transition
probability laws, derived from its proved expectation semigroup law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereKernelLaw
open HardSphereDynamics ActualSphereTransition ActualSphereSemigroup
set_option maxHeartbeats 1800000
variable {N p : ℕ}

/-- Transition expectations are exactly integrals against the actual
transition probability, for every strongly measurable observable. -/
theorem transition_eq_kernel_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ)
    (hf : StronglyMeasurable f) (x : State N) :
    transition D β R hR J t f x = ∫ y,f y ∂transitionKernel D β R hR J t x := by
  rw [transitionKernel_apply]
  exact (integral_map (((terminal_measurable D β R hR J t).comp
    (measurable_const.prodMk measurable_id)).aemeasurable) hf.aestronglyMeasurable).symm

/-- Literal genuine Chapman–Kolmogorov equality of probability measures
for every physical sphere initial state. -/
theorem transitionKernel_semigroup (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (s t : ℝ≥0) (x : State N) (hx : OnSphere x) :
    transitionKernel (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (s+t) x =
      (transitionKernel (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t ∘ₖ
        transitionKernel (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s) x := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let K := transitionKernel D β R hR J
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hfi : Integrable (fun y => f y) ((K t ∘ₖ K s) x) :=
    Integrable.of_bound f.continuous.stronglyMeasurable.aestronglyMeasurable ‖f‖
      (.of_forall (fun y => f.norm_coe_le_norm y))
  calc
    _ = transition D β R hR J (s+t) f x :=
      (transition_eq_kernel_integral D β R hR J (s+t) f f.continuous.stronglyMeasurable x).symm
    _ = transition D β R hR J s (transition D β R hR J t f) x :=
      transition_semigroup hN β R hR hNR J s t f f.continuous ‖f‖
        (fun y => f.norm_coe_le_norm y) x hx
    _ = ∫ z,transition D β R hR J t f z ∂K s x :=
      transition_eq_kernel_integral D β R hR J s (transition D β R hR J t f)
        (transition_measurable D β R hR J t f f.continuous) x
    _ = ∫ z,∫ y,f y ∂K t z ∂K s x := by
      apply integral_congr_ae
      exact .of_forall (fun z => transition_eq_kernel_integral D β R hR J t f
        f.continuous.stronglyMeasurable z)
    _ = _ := (Kernel.integral_comp hfi).symm

end SphericalAging.ActualSphereKernelLaw
