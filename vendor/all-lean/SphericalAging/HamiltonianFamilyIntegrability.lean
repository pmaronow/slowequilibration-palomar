module

public import SphericalAging.HamiltonianCoefficientDependence

public section

/-! Actual square integrability of the Hamiltonian coefficient families
under unbounded disorder laws. Compact cutoff bounds are uniform in the
state and grow only linearly in the finite Gaussian coupling; no artificial
bounded-disorder support or exponential parameter moment is assumed.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianFamilyIntegrability
open HardSphereDynamics LocalSDE HamiltonianParameter HamiltonianPicardDependence
open HamiltonianCoefficientDependence GlobalHamiltonianParameter
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1800000

/-- A true pointwise bounded coefficient has the exact finite-time L²
bound in the actual predictable coefficient class. -/
lemma norm_predictableCoefficient_le_of_bound {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U : PredictableStateL2 N F P) (T : ℝ≥0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C) :
    ‖predictableCoefficient hg U T‖ ≤ C * (PicardDependence.initialScale (P := P) T : ℝ) := by
  let W := (memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
      (measurableSet_Ioc.prod MeasurableSet.univ) C
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).toLp
        ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => C))
  have hw : ‖W‖ = C * (PicardDependence.initialScale (P := P) T : ℝ) := norm_indicator_toLp T C hC
  rw [← hw]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [predictableCoefficient_coeFn hg U T,
    (memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
      (measurableSet_Ioc.prod MeasurableSet.univ) C
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).coeFn_toLp] with q hq hwq
  change ‖(predictableCoefficient hg U T : TimeProcessL2 P) q‖ ≤ ‖(W : ℝ≥0 × Ω → ℝ) q‖
  change (W : ℝ≥0 × Ω → ℝ) q = _ at hwq
  rw [hq,hwq]
  by_cases hqt : q.1 ∈ Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hqt,mem_univ _⟩)]
    simp only [ite_eq_left hqt,Real.norm_of_nonneg hC]
    exact hbound _
  · rw [indicator_of_notMem (show q ∉ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from fun h => hqt h.1)]
    simp only [ite_eq_right hqt,norm_zero]
    exact le_rfl

/-- Uniform state-independent cutoff drift growth, affine in actual
disorder norm. -/
theorem cutoffDrift_uniform_growth (β R : ℝ) (hR : 0 < R) :
    ∃ C₀ C₁ : ℝ≥0, ∀ (J : FiniteModel.Disorder N p) i x,
      ‖CutoffSDE.cutoffDrift β J R hR i x‖ ≤ (C₀ : ℝ)+(C₁ : ℝ)*‖J‖ := by
  obtain ⟨B,hB⟩ := CutoffSDE.cutoffDrift_bounded (N := N) (p := p) β 0 R hR
  obtain ⟨C,hC⟩ := cutoffDrift_disorder_lipschitz (N := N) (p := p) β R hR
  refine ⟨⟨max B 0,le_max_right _ _⟩,C,fun J i x => ?_⟩
  have hd : ‖CutoffSDE.cutoffDrift β J R hR i x-CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i x‖ ≤ (C : ℝ)*‖J‖ := by
    change ‖(cutoffCoefficient R hR (hamiltonianDrift β J) x) i-
      (cutoffCoefficient R hR (hamiltonianDrift β (0 : FiniteModel.Disorder N p)) x) i‖ ≤ _
    rw [← PiLp.sub_apply]
    simpa only [sub_zero] using (PiLp.norm_apply_le _ i).trans (hC J 0 x)
  calc
    _ = ‖(CutoffSDE.cutoffDrift β J R hR i x-CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i x)+
        CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i x‖ := by rw [sub_add_cancel]
    _ ≤ ‖CutoffSDE.cutoffDrift β J R hR i x-CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i x‖+
        ‖CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i x‖ := norm_add_le _ _
    _ ≤ (C : ℝ)*‖J‖+max B 0 := add_le_add hd ((hB i x).trans (le_max_left _ _))
    _ = _ := by change (C : ℝ)*‖J‖+max B 0=max B 0+(C : ℝ)*‖J‖; ring

/-- Actual drift coefficient families are square integrable whenever
the actual finite disorder has its ordinary second moment. -/
theorem driftClass_memLp (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T : ℝ≥0) (i : Fin N) {ρ : Measure (FiniteModel.Disorder N p × State N)}
    [IsProbabilityMeasure ρ] (hJ : MemLp (fun q : FiniteModel.Disorder N p × State N => q.1) 2 ρ) :
    MemLp (driftClass D β R hR T i) 2 ρ := by
  obtain ⟨C₀,C₁,hgrowth⟩ := cutoffDrift_uniform_growth (N := N) (p := p) β R hR
  have hm : MemLp (fun q : FiniteModel.Disorder N p × State N =>
      ((C₀ : ℝ)+(C₁ : ℝ)*‖q.1‖)*(PicardDependence.initialScale (P := P) T : ℝ)) 2 ρ :=
    ((memLp_const (C₀ : ℝ)).add (hJ.norm.const_mul (C₁ : ℝ))).mul_const _
  apply hm.of_le (driftClass_continuous D β R hR T i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_predictableCoefficient_le_of_bound
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩) i)
    (globalClass D β R hR T q) T _ (by positivity) (hgrowth q.1 i)

/-- Actual noise coefficient families have a uniform square-integrable
bound under every probability law on disorder and initial state. -/
theorem noiseClass_memLp (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T : ℝ≥0) (i j : Fin N) {ρ : Measure (FiniteModel.Disorder N p × State N)}
    [IsProbabilityMeasure ρ] : MemLp (noiseClass D β R hR T i j) 2 ρ := by
  obtain ⟨C,hC⟩ := CutoffSDE.cutoffNoise_bounded N R hR
  apply (memLp_const ((C : ℝ)*(PicardDependence.initialScale (P := P) T : ℝ))).of_le
    (noiseClass_continuous D β R hR T i j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_predictableCoefficient_le_of_bound (noise_family_lipschitz N R hR i j)
    (globalClass D β R hR T q) T _ C.coe_nonneg (hC i j)

end SphericalAging.HamiltonianFamilyIntegrability
