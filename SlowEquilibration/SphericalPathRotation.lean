module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalFinitePathRotation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section

/-! # Actual whole-path covariance on finite physical time horizons

Finite-dimensional covariance determines the full process law. A genuine
measurable continuous-path representative is constructed from the actual
SDE on a conull measurable set, and its law is supported on spherical paths.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalStationarySDE
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

def wholePath (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N)
    (ω : VectorBrownian.Space N) : ℝ≥0 → Vector N := fun t => mixedProcess μ J β x t ω

lemma wholePath_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) : Measurable (wholePath μ J β x) :=
  Measurable.of_eval fun t => mixedProcess_measurable μ J β x t

def wholePathRotation (U : Vector N ≃ₗᵢ[ℝ] Vector N) (p : ℝ≥0 → Vector N) :
    ℝ≥0 → Vector N := fun t => U (p t)

lemma wholePathRotation_measurable (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    Measurable (wholePathRotation U) :=
  Measurable.of_eval fun t => U.continuous.measurable.comp (measurable_pi_apply t)

/-- The entire law of the actual canonical diffusion path rotates with
the actual mixed field, for every physical initial point. -/
theorem wholePathLaw_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (x : Vector N) (hx : OnSphere x) :
    ((VectorBrownian.law N).map (wholePath μ J β x)).map (wholePathRotation U) =
      (VectorBrownian.law N).map (wholePath μ (rotatedDisorder U J) β (U x)) := by
  rw [Measure.map_map (wholePathRotation_measurable U) (wholePath_measurable μ J β x)]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    ((wholePathRotation_measurable U).comp (wholePath_measurable μ J β x)).aemeasurable
    (wholePath_measurable μ (rotatedDisorder U J) β (U x)).aemeasurable).mpr
  intro I
  have h := finitePathLaw_rotation hN μ J β U x hx I
  rw [Measure.map_map (rotateCoordinates_measurable U I) (restrictPath_measurable μ J β x I)] at h
  exact h

abbrev PathTime (T : ℝ≥0) := Icc (0 : ℝ≥0) T
abbrev ContinuousPath (N : ℕ) (T : ℝ≥0) := C(PathTime T,Vector N)

def pathGoodEvent (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) :
    Set (VectorBrownian.Space N) :=
  {ω | Continuous (fun t => mixedProcess μ J β x t ω) ∧ ∀ t, OnSphere (mixedProcess μ J β x t ω)}

lemma pathGoodEvent_ae (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ω ∈ pathGoodEvent μ J β x := by
  filter_upwards [mixedProcess_continuous μ J β x,mixedProcess_onSphere (by omega) μ J β x hx] with ω hc hs
  exact ⟨hc,hs⟩

def measurablePathGoodEvent (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) :
    Set (VectorBrownian.Space N) :=
  (toMeasurable (VectorBrownian.law N) (pathGoodEvent μ J β x)ᶜ)ᶜ

lemma measurablePathGoodEvent_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) : MeasurableSet (measurablePathGoodEvent μ J β x) :=
  (measurableSet_toMeasurable _ _).compl

lemma measurablePathGoodEvent_subset (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) : measurablePathGoodEvent μ J β x ⊆ pathGoodEvent μ J β x := by
  intro ω hω
  exact not_not.mp (fun hb => hω (subset_toMeasurable _ _ hb))

lemma measurablePathGoodEvent_ae (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ω ∈ measurablePathGoodEvent μ J β x := by
  have hz : (VectorBrownian.law N) (pathGoodEvent μ J β x)ᶜ=0 :=
    ae_iff.mp (pathGoodEvent_ae hN μ J β x hx)
  apply ae_iff.mpr
  change (VectorBrownian.law N) (measurablePathGoodEvent μ J β x)ᶜ=0
  simpa only [measurablePathGoodEvent,compl_compl,measure_toMeasurable] using hz

/-- A literal measurable continuous-path representative, identified with
the actual SDE at all times on a common event of full Wiener probability. -/
def continuousPathRepresentative (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) (T : ℝ≥0) (ω : VectorBrownian.Space N) : ContinuousPath N T := by
  classical
  exact
  if hω : ω ∈ measurablePathGoodEvent μ J β x then
    ⟨fun t => mixedProcess μ J β x t.1 ω,
      (measurablePathGoodEvent_subset μ J β x hω).1.comp continuous_subtype_val⟩
  else ContinuousMap.const _ x

lemma continuousPathRepresentative_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) (T : ℝ≥0) : Measurable (continuousPathRepresentative μ J β x T) := by
  classical
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  have hm : Measurable ((measurablePathGoodEvent μ J β x).piecewise
      (mixedProcess μ J β x t.1) (fun _ => x)) := (mixedProcess_measurable μ J β x t.1).piecewise
    (measurablePathGoodEvent_measurable μ J β x) (measurable_const (a := x))
  convert hm using 1
  funext ω
  by_cases hω : ω ∈ measurablePathGoodEvent μ J β x <;> simp [continuousPathRepresentative,hω,Set.piecewise]

lemma continuousPathRepresentative_ae_actual (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t : PathTime T,
      continuousPathRepresentative μ J β x T ω t=mixedProcess μ J β x t.1 ω := by
  filter_upwards [measurablePathGoodEvent_ae hN μ J β x hx] with ω hω
  intro t
  simp [continuousPathRepresentative,hω]

def pathLaw (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) (T : ℝ≥0) : Measure (ContinuousPath N T) :=
  (VectorBrownian.law N).map (continuousPathRepresentative μ J β x T)

instance pathLaw_probability (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) (T : ℝ≥0) : IsProbabilityMeasure (pathLaw μ J β x T) := by
  unfold pathLaw
  have hm := continuousPathRepresentative_measurable μ J β x T
  infer_instance

/-- The true path law lives on spherical continuous paths, at every time
including both endpoints, as in source lem:red-kernels. -/
theorem pathLaw_sphere_supported (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ p ∂pathLaw μ J β x T, ∀ t, OnSphere (p t) := by
  classical
  unfold pathLaw
  have hS : MeasurableSet {p : ContinuousPath N T | ∀ t, OnSphere (p t)} := by
    have he : {p : ContinuousPath N T | ∀ t, OnSphere (p t)} =
        ⋂ t : PathTime T, {p : ContinuousPath N T | inner ℝ (p t) (p t)=(N:ℝ)} := by
      ext p
      simp only [mem_ofPred_eq,mem_iInter,OnSphere]
    rw [he]
    exact (isClosed_iInter fun t => isClosed_eq
      (by fun_prop : Continuous (fun p : ContinuousPath N T => inner ℝ (p t) (p t))) continuous_const).measurableSet
  apply (ae_map_iff (continuousPathRepresentative_measurable μ J β x T).aemeasurable
    hS).mpr
  exact .of_forall fun ω t => by
    by_cases hω : ω ∈ measurablePathGoodEvent μ J β x
    · simpa [continuousPathRepresentative,hω] using (measurablePathGoodEvent_subset μ J β x hω).2 t.1
    · simpa [continuousPathRepresentative,hω] using hx

def continuousPathRotation (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0)
    (p : ContinuousPath N T) : ContinuousPath N T :=
  (⟨U,U.continuous⟩ : C(Vector N,Vector N)).comp p

lemma continuousPathRotation_measurable (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0) :
    Measurable (continuousPathRotation U T) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact U.continuous.measurable.comp ((ProbabilityTheory.ContinuousMap.measurable_iff_eval
    (g := fun p : ContinuousPath N T => p)).mp measurable_id t)

def pathEval {T : ℝ≥0} (p : ContinuousPath N T) : PathTime T → Vector N := fun t => p t

lemma pathEval_measurable (T : ℝ≥0) : Measurable (pathEval (N := N) (T := T)) :=
  Measurable.of_eval fun t => (ProbabilityTheory.ContinuousMap.measurable_iff_eval
    (g := fun p : ContinuousPath N T => p)).mp measurable_id t

/-- Actual continuous-path measures are determined by their ordinary full
evaluation law. This follows from the proved Borel evaluation σ-algebra. -/
lemma continuousPathMeasure_ext {T : ℝ≥0} (M₁ M₂ : Measure (ContinuousPath N T))
    (he : M₁.map pathEval=M₂.map pathEval) : M₁=M₂ := by
  have hm : (inferInstance : MeasurableSpace (ContinuousPath N T)) =
      MeasurableSpace.pi.comap (pathEval (N := N) (T := T)) := by
    calc
      _ = ⨆ t : PathTime T, (inferInstance : MeasurableSpace (Vector N)).comap
          (fun p : ContinuousPath N T => p t) := ProbabilityTheory.ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ = _ := by simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,MeasurableSpace.comap_comp,
        pathEval,Function.comp_def]
  ext S hS
  change @MeasurableSet (ContinuousPath N T) (inferInstance : MeasurableSpace (ContinuousPath N T)) S at hS
  rw [hm] at hS
  obtain ⟨B,hB,rfl⟩ := hS
  rw [← Measure.map_apply (pathEval_measurable T) hB,← Measure.map_apply (pathEval_measurable T) hB]
  exact congrArg (fun M : Measure (PathTime T → Vector N) => M B) he

/-- Source lem:red-kernels path-law covariance on every finite horizon,
for the literal mixed SDE law on continuous spherical paths. -/
theorem pathLaw_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) (hx : OnSphere x) (T : ℝ≥0) :
    (pathLaw μ J β x T).map (continuousPathRotation U T)=
      pathLaw μ (rotatedDisorder U J) β (U x) T := by
  apply continuousPathMeasure_ext
  rw [pathLaw,pathLaw,Measure.map_map (pathEval_measurable T) (continuousPathRotation_measurable U T),
    Measure.map_map ((pathEval_measurable T).comp (continuousPathRotation_measurable U T))
      (continuousPathRepresentative_measurable μ J β x T),
    Measure.map_map (pathEval_measurable T) (continuousPathRepresentative_measurable μ (rotatedDisorder U J) β (U x) T)]
  let restrict : (ℝ≥0 → Vector N) → PathTime T → Vector N := fun p t => p t.1
  have hr : Measurable restrict := Measurable.of_eval fun t => measurable_pi_apply t.1
  have hw := congrArg (fun M : Measure (ℝ≥0 → Vector N) => M.map restrict)
    (wholePathLaw_rotation hN μ J β U x hx)
  rw [Measure.map_map hr (wholePathRotation_measurable U),
    Measure.map_map (hr.comp (wholePathRotation_measurable U)) (wholePath_measurable μ J β x),
    Measure.map_map hr (wholePath_measurable μ (rotatedDisorder U J) β (U x))] at hw
  calc
    _ = (VectorBrownian.law N).map (restrict ∘ wholePathRotation U ∘ wholePath μ J β x) := by
      apply Measure.map_congr
      filter_upwards [continuousPathRepresentative_ae_actual hN μ J β x hx T] with ω hω
      funext t
      exact congrArg U (hω t)
    _ = (VectorBrownian.law N).map (restrict ∘ wholePath μ (rotatedDisorder U J) β (U x)) := hw
    _ = _ := by
      apply Measure.map_congr
      filter_upwards [continuousPathRepresentative_ae_actual hN μ (rotatedDisorder U J) β (U x) (onSphere_map U hx) T] with ω hω
      funext t
      exact (hω t).symm

end
end SlowEquilibration.SphericalRotationCovariance
