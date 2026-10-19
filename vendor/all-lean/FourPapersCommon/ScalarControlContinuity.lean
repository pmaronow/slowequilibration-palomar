module
public import FourPapersCommon.ScalarBrownianControl
public import FourPapersCommon.ClockedStateContinuity
public import FourPapersCommon.L2ObservableBound

@[expose] public section

/-! Genuine endpoint continuity for every bounded adapted scalar Brownian
control. The estimate uses the actual Brownian increment covariance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem norm_scalarControlDrift_le (m : ℝ) (A : ℝ → BrownianSample → ℝ)
    (K : ℝ≥0) (hK : ∀ s ω, ‖A s ω‖ ≤ K) (s : ℝ≥0) (ω : BrownianSample) :
    ‖scalarControlDrift m A s ω‖ ≤ |m| *(K : ℝ) := by
  rw [scalarControlDrift,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hK s ω) (abs_nonneg m)

theorem memLp_scalarControlledState (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) (t : ℝ≥0) :
    MemLp (scalarControlledState m x A t) 2 canonicalBrownianMeasure := by
  obtain ⟨K,hK⟩ := hA.bounded
  let D : ℝ≥0 := ⟨|m| *(K : ℝ),mul_nonneg (abs_nonneg m) K.2⟩
  have hi : MemLp (integratedDrift (scalarControlDrift m A) t) 2 canonicalBrownianMeasure :=
    .of_bound (stronglyMeasurable_integratedDrift (measurable_scalarControlDrift m A hA) t).aestronglyMeasurable
      ((D : ℝ)*(t : ℝ)) (.of_forall fun ω =>
        norm_integratedDrift_le_of_bound D (norm_scalarControlDrift_le m A K hK) t ω)
  change MemLp (fun ω => x+integratedDrift (scalarControlDrift m A) t ω+canonicalBrownian t ω)
    2 canonicalBrownianMeasure
  exact ((memLp_const x).add hi).add (memLp_timeChangedBrownian id t)

theorem scalarControlledState_increment_square_le (m x : ℝ) (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) (K : ℝ≥0) (hK : ∀ s ω, ‖A s ω‖ ≤ K)
    (s t : ℝ≥0) :
    (∫ ω,(scalarControlledState m x A s ω-scalarControlledState m x A t ω)^2
      ∂canonicalBrownianMeasure) ≤
      2*(|m| *(K : ℝ))^2*((s : ℝ)-(t : ℝ))^2+2*dist s t := by
  let μ := scalarControlDrift m A
  let X := scalarControlledState m x A
  let W := timeChangedBrownian id
  let D : ℝ≥0 := ⟨|m| *(K : ℝ),mul_nonneg (abs_nonneg m) K.2⟩
  have hiX := ((memLp_scalarControlledState m x A hA s).sub
    (memLp_scalarControlledState m x A hA t)).integrable_sq
  have hiW := integrable_timeChangedBrownian_increment_square id id s t
  have hpoint (ω : BrownianSample) : (X s ω-X t ω)^2 ≤
      2*(D : ℝ)^2*((s : ℝ)-(t : ℝ))^2+2*(W s ω-W t ω)^2 := by
    have hn := norm_integratedDrift_sub_le μ (measurable_scalarControlDrift m A hA)
      D (norm_scalarControlDrift_le m A K hK) s t ω
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg D.2 (abs_nonneg _))).mpr hn
    simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hsq
    have he : X s ω-X t ω = (integratedDrift μ s ω-integratedDrift μ t ω)+(W s ω-W t ω) := by
      dsimp [X,μ,W,scalarControlledState,timeChangedBrownian]
      ring
    rw [he]
    calc
      _ ≤ 2*(integratedDrift μ s ω-integratedDrift μ t ω)^2+2*(W s ω-W t ω)^2 := by
        nlinarith only [sq_nonneg ((integratedDrift μ s ω-integratedDrift μ t ω)-(W s ω-W t ω))]
      _ ≤ _ := by
        have hm2 : 2*(integratedDrift μ s ω-integratedDrift μ t ω)^2 ≤
            2*((D : ℝ)^2*((s : ℝ)-(t : ℝ))^2) :=
          mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)
        calc
          _ ≤ 2*((D : ℝ)^2*((s : ℝ)-(t : ℝ))^2)+2*(W s ω-W t ω)^2 :=
            add_le_add hm2 le_rfl
          _ = _ := by ring
  have hmono := integral_mono hiX
    ((integrable_const (2*(D : ℝ)^2*((s : ℝ)-(t : ℝ))^2)).add (hiW.const_mul 2)) hpoint
  change (∫ ω,(X s ω-X t ω)^2 ∂canonicalBrownianMeasure) ≤
    (∫ ω,2*(D : ℝ)^2*((s : ℝ)-(t : ℝ))^2+2*(W s ω-W t ω)^2 ∂canonicalBrownianMeasure) at hmono
  rw [integral_add (f := fun _ => 2*(D : ℝ)^2*((s : ℝ)-(t : ℝ))^2)
    (g := fun ω => 2*(W s ω-W t ω)^2) (integrable_const _) (hiW.const_mul 2),
    integral_const,integral_const_mul] at hmono
  simp only [MeasureTheory.probReal_univ,one_smul] at hmono
  rw [timeChangedBrownian_increment_square] at hmono
  exact hmono

theorem tendsto_integral_abs_scalarControlledState_increment (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) (r : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ ω,|scalarControlledState m x A t ω-scalarControlledState m x A r ω|
      ∂canonicalBrownianMeasure) (𝓝 r) (𝓝 0) := by
  obtain ⟨K,hK⟩ := hA.bounded
  have hsq : Tendsto (fun t : ℝ≥0 => ∫ ω,
      (scalarControlledState m x A t ω-scalarControlledState m x A r ω)^2
      ∂canonicalBrownianMeasure) (𝓝 r) (𝓝 0) := by
    apply squeeze_zero (fun t => integral_nonneg (fun ω => sq_nonneg _))
      (scalarControlledState_increment_square_le m x A hA K hK · r)
    have hc : Continuous (fun t : ℝ≥0 =>
        2*(|m| *(K : ℝ))^2*((t : ℝ)-(r : ℝ))^2+2*dist t r) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := r)
  apply squeeze_zero (fun t => integral_nonneg (fun ω => abs_nonneg _))
    (fun t => integral_abs_le_sqrt_square _
      ((memLp_scalarControlledState m x A hA t).sub (memLp_scalarControlledState m x A hA r)))
  simpa only [Real.sqrt_zero,Function.comp_def,Pi.sub_apply] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

end FourPapersCommon
