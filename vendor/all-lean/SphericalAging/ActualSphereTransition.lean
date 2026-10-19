module

public import SphericalAging.HamiltonianJointProcess
public import SphericalAging.PhysicalVariationalMoments
public import Mathlib.Probability.Kernel.Composition.Prod
public import SphericalAging.GaussianObservableDerivative

public section

/-! Genuine transition kernels and expectations of the constructed
fixed-disorder Hamiltonian SDE. Joint measurability comes from the actual
Picard solution family; support and the conditional-mean norm bound come
from sphere preservation. No Markov or PDE identity is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereTransition
open HardSphereDynamics HamiltonianJointProcess HamiltonianPicardDependence
open GlobalHamiltonianParameter
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- A measurable version of the actual all-time SDE family. -/
@[expose] def jointProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) :
    (FiniteModel.Disorder N p × State N) → ℝ≥0 → Ω → State N :=
  (exists_joint_adapted_global_process (p := p) D β R hR).choose

lemma jointProcess_measurable (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) :
    StronglyMeasurable (fun q : (FiniteModel.Disorder N p × State N) × (ℝ≥0 × Ω) =>
      jointProcess D β R hR q.1 q.2.1 q.2.2) :=
  (exists_joint_adapted_global_process D β R hR).choose_spec.1

lemma jointProcess_adapted (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace (FiniteModel.Disorder N p × State N)).prod (F t)]
      (fun q : (FiniteModel.Disorder N p × State N) × Ω => jointProcess D β R hR q.1 t q.2) :=
  (exists_joint_adapted_global_process D β R hR).choose_spec.2.1 t

lemma jointProcess_ae (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (q : FiniteModel.Disorder N p × State N) :
    ∀ᵐ ω ∂P, ∀ t, jointProcess D β R hR q t ω = globalProcess D β R hR q t ω :=
  ((exists_joint_adapted_global_process D β R hR).choose_spec.2.2 q).mono (fun _ h => h.1)

lemma terminal_measurable (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) :
    Measurable (fun q : State N × Ω => jointProcess D β R hR (J,q.1) t q.2) := by
  exact (jointProcess_measurable D β R hR).measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd))

/-- Actual transition probability on the ambient Euclidean state space.
Its restriction to sphere initial states is supported on the physical sphere. -/
@[expose] def transitionKernel (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) : Kernel (State N) (State N) :=
  (Kernel.id ×ₖ Kernel.const (State N) P).map
    (fun q : State N × Ω => jointProcess D β R hR (J,q.1) t q.2)

instance transitionKernel_markov (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) :
    IsMarkovKernel (transitionKernel D β R hR J t) :=
  Kernel.IsMarkovKernel.map _ (terminal_measurable D β R hR J t)

/-- Each transition is the law of the actual terminal solution. -/
theorem transitionKernel_apply (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) :
    transitionKernel D β R hR J t x =
      P.map (fun ω => jointProcess D β R hR (J,x) t ω) := by
  rw [transitionKernel,Kernel.map_apply _ (terminal_measurable D β R hR J t),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (terminal_measurable D β R hR J t) measurable_prodMk_left]
  rfl

/-- Genuine fixed-disorder transition expectation. -/
@[expose] def transition (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ) (x : State N) : ℝ :=
  ∫ ω, f (jointProcess D β R hR (J,x) t ω) ∂P

/-- The jointly measurable version does not change the actual SDE expectation. -/
theorem transition_eq_actual (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ) (x : State N) :
    transition D β R hR J t f x = ∫ ω,f (globalProcess D β R hR (J,x) t ω) ∂P := by
  apply integral_congr_ae
  exact (jointProcess_ae D β R hR (J,x)).mono (fun _ h => congrArg f (h t))

lemma transition_integrable (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : State N) :
    Integrable (fun ω => f (jointProcess D β R hR (J,x) t ω)) P := by
  apply Integrable.of_bound
    (hf.measurable.comp ((terminal_measurable D β R hR J t).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable C
  exact .of_forall (fun ω => hC _)

/-- Transition expectations are centered at the prescribed initial state at time zero. -/
theorem transition_zero (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (f : State N → ℝ) (x : State N) :
    transition D β R hR J 0 f x = f x := by
  rw [transition_eq_actual]
  apply integral_eq_const
  have hi := (GlobalSDE.process_strongSolution D
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (noise_family_lipschitz N R hR) x 0).initial
  exact hi.mono (fun _ h => congrArg f h)

lemma transition_const (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (c : ℝ) (x : State N) :
    transition D β R hR J t (fun _ => c) x = c := by simp [transition]

lemma transition_bound (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : State N) :
    ‖transition D β R hR J t f x‖ ≤ C := by
  simpa only [transition,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := P) (.of_forall (fun ω => hC _))

/-- The actual global family preserves the sphere on a common all-time event. -/
theorem globalProcess_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) :
    ∀ᵐ ω ∂P,∀ t,OnSphere (globalProcess (NullAugmentation.driver D₀) β R hR (J,x) t ω) := by
  have hall := ae_all_iff.mpr (fun n : ℕ =>
    PhysicalVariationalMoments.horizonProcess_onSphere hN D₀ β J R hR hNR x hx
      (GlobalSDE.integerHorizon n)
      (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR))
  filter_upwards [hall] with ω hω
  intro t
  exact hω (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

lemma jointProcess_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) :
    ∀ᵐ ω ∂P,∀ t,OnSphere (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t ω) := by
  filter_upwards [jointProcess_ae (NullAugmentation.driver D₀) β R hR (J,x),
    globalProcess_onSphere hN D₀ β R hR hNR J x hx] with ω he hs
  intro t
  rw [he t]
  exact hs t

/-- Actual expected state, rather than an independently supplied PDE mean. -/
@[expose] def mean (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) : State N :=
  ∫ ω,jointProcess D β R hR (J,x) t ω ∂P

/-- Sphere preservation gives the exact norm bound required by FDT. -/
theorem mean_norm_sq_le (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) (hx : OnSphere x) :
    ‖mean (NullAugmentation.driver D₀) β R hR J t x‖^2 ≤ (N : ℝ) := by
  have hb : ∀ᵐ ω ∂P,‖jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t ω‖ ≤ Real.sqrt (N : ℝ) := by
    filter_upwards [jointProcess_onSphere hN D₀ β R hR hNR J x hx] with ω hω
    exact le_of_eq (LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω t)))
  have hm : ‖mean (NullAugmentation.driver D₀) β R hR J t x‖ ≤ Real.sqrt (N : ℝ) := by
    simpa only [mean,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb
  nlinarith [norm_nonneg (mean (NullAugmentation.driver D₀) β R hR J t x),
    Real.sqrt_nonneg (N : ℝ),Real.sq_sqrt (Nat.cast_nonneg N)]

end SphericalAging.ActualSphereTransition
