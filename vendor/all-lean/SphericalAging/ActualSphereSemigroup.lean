module

public import SphericalAging.ActualSphereMarkovRestart

public section

/-! The genuine Chapman–Kolmogorov expectation law of the fixed-disorder
sphere SDE. The restart identity uses the actual future Wiener path,
its product law with the observed waiting state, and actual SDE uniqueness.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereSemigroup
open HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
open AnnealedSDECore BrownianFuturePath BrownianFutureFiltered
set_option maxHeartbeats 2200000
variable {N p : ℕ}

/-- Bounded continuous tests have measurable actual transition expectations. -/
lemma transition_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ) (hf : Continuous f) :
    StronglyMeasurable (transition D β R hR J t f) :=
  (hf.stronglyMeasurable.comp_measurable (terminal_measurable D β R hR J t)).integral_prod_right'

/-- Actual future observables have the transition expectation at the
actual random waiting state. No Markov identity is a hypothesis. -/
theorem restart_expectation (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (X : ℝ≥0 → VectorBrownian.Space N → State N)
    {Z0 : VectorBrownian.Space N → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) (s t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ x,‖f x‖ ≤ C) :
    (∫ ω,f (X (s+t) ω) ∂VectorBrownian.law N) =
      ∫ ω,transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f (X s ω)
        ∂VectorBrownian.law N := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  have hXa := (hX 0).2.1
  have hXm : Measurable (X s) := ((hXa s).mono ((NullAugmentation.augment
    (VectorBrownian.filtration N) P).le s)).measurable
  let μ := P.map (X s)
  have hμ : IsProbabilityMeasure μ :=
    (hasLaw_map hXm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  letI := hμ
  let G : State N × VectorBrownian.Space N → ℝ :=
    fun q => f (jointProcess D β R hR (J,q.1) t q.2)
  have hG : StronglyMeasurable G :=
    hf.stronglyMeasurable.comp_measurable (terminal_measurable D β R hR J t)
  have hGi : Integrable G (μ.prod P) :=
    Integrable.of_bound hG.aestronglyMeasurable C (.of_forall (fun _ => hC _))
  let φ : VectorBrownian.Space N → State N × VectorBrownian.Space N := fun ω => (X s ω,future s ω)
  have hφ : MeasurePreserving φ P (μ.prod P) := waiting_future_measurePreserving s (X s) (hXa s).measurable
  have hpull : (∫ ω,G (φ ω) ∂P) = ∫ q,G q ∂μ.prod P := by
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hG.aestronglyMeasurable).symm
  calc
    _ = ∫ ω,G (φ ω) ∂P := by
      apply integral_congr_ae
      exact (actual_future_eq_joint hN β R hR hNR J X hX hXs s t).mono
        (fun _ h => congrArg f h)
    _ = ∫ q,G q ∂μ.prod P := hpull
    _ = ∫ x,transition D β R hR J t f x ∂μ := integral_prod G hGi
    _ = _ := integral_map hXm.aemeasurable
      (transition_measurable D β R hR J t f hf).aestronglyMeasurable

/-- Genuine fixed-disorder Chapman–Kolmogorov law for actual sphere transition expectations. -/
theorem transition_semigroup (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (s t : ℝ≥0) (f : State N → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x,‖f x‖ ≤ C) (x : State N) (hx : OnSphere x) :
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (s+t) f x =
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s
        (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f) x := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  exact restart_expectation hN β R hR hNR J X
    (fun T => jointProcess_physical hN (VectorBrownian.driver N) β R hR hNR J x hx T)
    (jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx) s t f hf C hC

end SphericalAging.ActualSphereSemigroup
