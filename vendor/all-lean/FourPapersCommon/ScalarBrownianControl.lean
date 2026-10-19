module
public import Paper.ParisiControlledState

@[expose] public section

/-! Actual scalar Brownian states for arbitrary signed bounded adapted drifts.
The control class supplies regularity of the control only; the state, all its
Itô characteristics, and endpoint integrability are proved here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

structure IsScalarBrownianControl (A : ℝ → BrownianSample → ℝ) : Prop where
  continuous_paths : ∀ ω,Continuous (fun s=>A s ω)
  adapted : StronglyAdapted canonicalBrownianFiltration (fun s ω=>A s ω)
  measurable : Measurable (Function.uncurry A)
  bounded : ∃ K : ℝ≥0,∀ s ω,‖A s ω‖≤K

def scalarControlDrift (m : ℝ) (A : ℝ → BrownianSample → ℝ)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ := m*A t ω

def scalarControlledState (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  x+integratedDrift (scalarControlDrift m A) t ω+canonicalBrownian t ω

theorem measurable_scalarControlDrift (m : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) : Measurable (Function.uncurry (scalarControlDrift m A)) :=
  measurable_const.mul (hA.measurable.comp (measurable_fst.coe_nnreal_real.prodMk measurable_snd))

theorem scalarControlDrift_intervalIntegrable (m : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) (a b : ℝ) (ω : BrownianSample) :
    IntervalIntegrable (fun s : ℝ=>scalarControlDrift m A s.toNNReal ω) volume a b := by
  exact (continuous_const.mul ((hA.continuous_paths ω).comp
    (NNReal.continuous_coe.comp continuous_real_toNNReal))).intervalIntegrable a b

theorem continuous_scalarControlledState (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) (ω : BrownianSample) :
    Continuous (fun t=>scalarControlledState m x A t ω) := by
  have hi : Continuous (fun t : ℝ≥0=>integratedDrift (scalarControlDrift m A) t ω) := by
    have he (t : ℝ≥0) : integratedDrift (scalarControlDrift m A) t ω=
        ∫ s in 0..(t : ℝ),scalarControlDrift m A s.toNNReal ω := by
      rw [integratedDrift,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le t.coe_nonneg]
    simp_rw [he]
    exact (intervalIntegral.continuous_primitive
      (fun a b=>scalarControlDrift_intervalIntegrable m A hA a b ω) (0 : ℝ)).comp NNReal.continuous_coe
  exact (continuous_const.add hi).add (continuous_canonicalBrownian ω)

theorem stronglyProgressive_scalarControlDrift (m : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) :
    IsStronglyProgressive canonicalBrownianFiltration (scalarControlDrift m A) := by
  have hp := hA.adapted.isStronglyProgressive_of_continuous
    (fun ω=>(hA.continuous_paths ω).comp NNReal.continuous_coe)
  intro t
  let : MeasurableSpace BrownianSample := canonicalBrownianFiltration t
  exact ((hp t).const_mul m)

theorem stronglyAdapted_integrated_scalarControlDrift (m : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) :
    StronglyAdapted canonicalBrownianFiltration (integratedDrift (scalarControlDrift m A)) := by
  have hp := stronglyProgressive_scalarControlDrift m A hA
  intro t
  let : MeasurableSpace BrownianSample := canonicalBrownianFiltration t
  let clamp : ℝ≥0 → Iic t := fun s=>⟨min s t,mem_Iic.mpr (min_le_right _ _)⟩
  have hc : Measurable clamp := (measurable_id.min measurable_const).subtype_mk
  have hm : Measurable (Function.uncurry (fun s ω=>scalarControlDrift m A (min s t) ω)) :=
    (hp t).measurable.comp ((hc.comp measurable_fst).prodMk measurable_snd)
  convert stronglyMeasurable_integratedDrift hm t using 1
  funext ω
  unfold integratedDrift
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hst : s.toNNReal≤t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hs.1]
    exact hs.2
  dsimp only
  rw [min_eq_left hst]

theorem stronglyAdapted_scalarControlledState (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) :
    StronglyAdapted canonicalBrownianFiltration (scalarControlledState m x A) := by
  intro t
  exact (stronglyMeasurable_const.add
    (stronglyAdapted_integrated_scalarControlDrift m A hA t)).add
    (Filtration.stronglyAdapted_natural
      (fun s=>(measurable_canonicalBrownian s).stronglyMeasurable) t)

theorem measurable_scalarControlledState (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) : Measurable (Function.uncurry (scalarControlledState m x A)) := by
  apply measurable_uncurry_of_continuous_of_measurable (continuous_scalarControlledState m x A hA)
  intro t
  exact ((stronglyAdapted_scalarControlledState m x A hA t).mono
    (canonicalBrownianFiltration.le t)).measurable

@[simp] theorem scalarControlledState_zero (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (ω : BrownianSample) : scalarControlledState m x A 0 ω=x := by
  simp [scalarControlledState,integratedDrift]

theorem scalarControlledState_decomposition (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (t : ℝ≥0) (ω : BrownianSample) :
    scalarControlledState m x A t ω=scalarControlledState m x A 0 ω+
      integratedDrift (scalarControlDrift m A) t ω+canonicalDiracShiftMartingale 1 0 t ω := by
  rw [scalarControlledState_zero]
  simp [scalarControlledState,canonicalDiracShiftMartingale]

theorem boundedDriftItoCharacteristics_scalarControlledState (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure canonicalBrownianFiltration
      (scalarControlledState m x A) (scalarControlDrift m A)
      (canonicalDiracShiftMartingale 1 0) 1 := by
  obtain ⟨K,hK⟩ := hA.bounded
  refine ⟨continuous_scalarControlledState m x A hA,
    stronglyAdapted_scalarControlledState m x A hA,measurable_scalarControlDrift m A hA,?_,
    scalarControlledState_decomposition m x A,?_,memLp_canonicalDiracShiftMartingale 1 0,?_⟩
  · refine ⟨⟨|m| *K,mul_nonneg (abs_nonneg m) K.2⟩,?_⟩
    intro s ω
    change ‖m*A s ω‖≤|m| *(K : ℝ)
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK s ω) (abs_nonneg m)
  · have hF : canonicalBrownianShiftFiltration 0=canonicalBrownianFiltration := by
      apply Filtration.ext
      funext t
      change canonicalBrownianFiltration (0+t)=canonicalBrownianFiltration t
      rw [zero_add]
    simpa only [hF] using martingale_canonicalDiracShiftMartingale 1 0
  · intro T r
    convert quadraticVariation_canonicalDiracShiftMartingale 1 0 T r using 1
    ext ω
    simp [integral_const,Measure.real,nonnegativeLebesgueMeasure_Ioc,smul_eq_mul,
      ENNReal.toReal_min,mul_comm]

theorem integrable_scalarControlledState (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) (t : ℝ≥0) :
    Integrable (scalarControlledState m x A t) canonicalBrownianMeasure := by
  apply (boundedDriftItoCharacteristics_scalarControlledState m x A hA).integrable_state
  have he : scalarControlledState m x A 0=(fun _=>x) :=
    funext (scalarControlledState_zero m x A)
  rw [he]
  exact integrable_const x

theorem scalarControlledState_terminal (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (ω : BrownianSample) : scalarControlledState m x A 1 ω=
      x+canonicalBrownian 1 ω+m*(∫ s in 0..(1 : ℝ),A s ω) := by
  have hi : integratedDrift (scalarControlDrift m A) 1 ω=m*(∫ s in 0..(1 : ℝ),A s ω) := by
    unfold integratedDrift scalarControlDrift
    simp only [NNReal.coe_one]
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
      intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s∈Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (show (0:ℝ)≤1 by norm_num)] using hs
    dsimp only
    rw [Real.coe_toNNReal _ hsI.1]
  rw [scalarControlledState,hi]
  ring

end FourPapersCommon
