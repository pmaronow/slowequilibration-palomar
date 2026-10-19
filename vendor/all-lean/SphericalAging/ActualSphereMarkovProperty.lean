module

public import SphericalAging.ActualSphereSemigroup
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

public section

/-! Genuine conditional Markov identities for the actual sphere SDE.
The conditional expectation is derived by testing all observed waiting
variables against the true independent future Wiener path law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereMarkovProperty
open HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart ActualSphereSemigroup
open AnnealedSDECore BrownianFuturePath BrownianFutureFiltered
set_option maxHeartbeats 2400000
variable {N p : ℕ}

/-- The actual future transition identity holds against every bounded
variable observed in the full null-augmented waiting filtration. -/
theorem waiting_test_identity (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (X : ℝ≥0 → VectorBrownian.Space N → State N)
    {Z0 : VectorBrownian.Space N → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) (s t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C)
    (H : VectorBrownian.Space N → ℝ)
    (hH : StronglyMeasurable[NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N) s] H) (B : ℝ≥0) (hB : ∀ ω,‖H ω‖ ≤ B) :
    (∫ ω,H ω*f (X (s+t) ω) ∂VectorBrownian.law N) =
      ∫ ω,H ω*transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f (X s ω)
        ∂VectorBrownian.law N := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  have hXa := (hX 0).2.1
  let Z : VectorBrownian.Space N → State N × ℝ := fun ω => (X s ω,H ω)
  have hZa : Measurable[F s] Z := (hXa s).measurable.prodMk hH.measurable
  have hZm : Measurable Z := hZa.mono (F.le s) le_rfl
  let μ := P.map Z
  have hμ : IsProbabilityMeasure μ :=
    (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  letI := hμ
  have hboundμ : ∀ᵐ z ∂μ,‖z.2‖ ≤ B :=
    (ae_map_iff hZm.aemeasurable (measurableSet_le measurable_snd.norm measurable_const)).mpr
      (.of_forall hB)
  let G : (State N × ℝ) × VectorBrownian.Space N → ℝ :=
    fun q => q.1.2*f (jointProcess D β R hR (J,q.1.1) t q.2)
  have hG : StronglyMeasurable G :=
    (measurable_snd.comp measurable_fst).stronglyMeasurable.mul
      (hf.stronglyMeasurable.comp_measurable ((terminal_measurable D β R hR J t).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have hGi : Integrable G (μ.prod P) := by
    apply Integrable.of_bound hG.aestronglyMeasurable ((B : ℝ)*C)
    have hb := (measurePreserving_fst (μ := μ) (ν := P)).quasiMeasurePreserving.ae hboundμ
    filter_upwards [hb] with q hq
    exact (norm_mul _ _).trans_le (mul_le_mul hq (hC _) (norm_nonneg _) B.coe_nonneg)
  let φ : VectorBrownian.Space N → (State N × ℝ) × VectorBrownian.Space N :=
    fun ω => (Z ω,future s ω)
  have hφ : MeasurePreserving φ P (μ.prod P) := waiting_future_measurePreserving s Z hZa
  have hpull : (∫ ω,G (φ ω) ∂P) = ∫ q,G q ∂μ.prod P := by
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hG.aestronglyMeasurable).symm
  calc
    _ = ∫ ω,G (φ ω) ∂P := by
      apply integral_congr_ae
      exact (actual_future_eq_joint hN β R hR hNR J X hX hXs s t).mono
        (fun ω h => congrArg (fun z => H ω*f z) h)
    _ = ∫ q,G q ∂μ.prod P := hpull
    _ = ∫ z,z.2*transition D β R hR J t f z.1 ∂μ := by
      rw [integral_prod G hGi]
      apply integral_congr_ae
      exact .of_forall (fun z => integral_const_mul z.2 _)
    _ = _ := integral_map hZm.aemeasurable
      ((measurable_snd.stronglyMeasurable).mul
        ((transition_measurable D β R hR J t f hf).comp_measurable measurable_fst)).aestronglyMeasurable

/-- The true conditional expectation in the full waiting filtration is
exactly the actual transition expectation at the observed state. -/
theorem conditional_transition (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (X : ℝ≥0 → VectorBrownian.Space N → State N)
    {Z0 : VectorBrownian.Space N → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) (s t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C) :
    (VectorBrownian.law N)[(fun ω => f (X (s+t) ω)) |
      NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s] =ᵐ[VectorBrownian.law N]
      (fun ω => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f (X s ω)) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let g : VectorBrownian.Space N → ℝ := fun ω => transition D β R hR J t f (X s ω)
  have hXa := (hX 0).2.1
  have hga : StronglyMeasurable[F s] g :=
    (transition_measurable D β R hR J t f hf).comp_measurable (hXa s).measurable
  have hgi : Integrable g P := Integrable.of_bound
    (hga.mono (F.le s)).aestronglyMeasurable C
      (.of_forall (fun ω => transition_bound D β R hR J t f C hC _))
  have hfi : Integrable (fun ω => f (X (s+t) ω)) P := Integrable.of_bound
    (hf.comp_stronglyMeasurable ((hXa (s+t)).mono (F.le (s+t)))).aestronglyMeasurable C
      (.of_forall (fun ω => hC _))
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) hfi
    (fun S _ _ => hgi.integrableOn) ?_ hga.aestronglyMeasurable
  intro S hS _
  let H : VectorBrownian.Space N → ℝ := S.indicator (fun _ => 1)
  have hH : StronglyMeasurable[F s] H := stronglyMeasurable_const.indicator hS
  have hHb : ∀ ω,‖H ω‖ ≤ (1 : ℝ≥0) := by
    intro ω
    by_cases hω : ω ∈ S <;> simp [H,hω]
  have h := waiting_test_identity hN β R hR hNR J X hX hXs s t f hf C hC H hH 1 hHb
  have hSambient : MeasurableSet S := F.le s S hS
  have hgH : (fun ω => H ω*g ω) = S.indicator g := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [H,hω]
  have hfH : (fun ω => H ω*f (X (s+t) ω)) =
      S.indicator (fun ω => f (X (s+t) ω)) := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [H,hω]
  change (∫ ω,H ω*f (X (s+t) ω) ∂P) = ∫ ω,H ω*g ω ∂P at h
  rw [hgH,hfH,integral_indicator hSambient,integral_indicator hSambient] at h
  exact h.symm

end SphericalAging.ActualSphereMarkovProperty
