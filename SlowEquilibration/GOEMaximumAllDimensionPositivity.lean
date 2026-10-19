-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEAllShiftPositivity
public import SlowEquilibration.GOEMaximumDeterminant

/-! Genuine all-dimension positivity of the determinant mean restricted to
negative Hessians. An actual open Gaussian coefficient neighborhood of zero
has strictly positive mass and remains below every positive shift. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEMaximumDeterminant
open Set MeasureTheory ProbabilityTheory Function
open SphericalGaussianJet UnrestrictedConditionedDeterminants GOEAllShiftPositivity
open GOEAsymptotics GOERawMoments OAI.CriticalSK
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxHeartbeats 100000

theorem maximumMean_pos_all_dimensions (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b k : ℝ} (hb : 0 < b) (hk : 0 < k) : 0 < maximumMean n N b k := by
  let V : UpperIndex (n+1) → ℝ≥0 := fun ij =>
    ((b/(N : ℝ))*(if ij.val.1=ij.val.2 then 2 else 1)).toNNReal
  have hV (ij : UpperIndex (n+1)) : V ij ≠ 0 := by
    apply ne_of_gt
    apply Real.toNNReal_pos.mpr
    have hd : 0 < b/(N : ℝ) := div_pos hb (Nat.cast_pos.mpr hN)
    split_ifs <;> positivity
  let (ij : UpperIndex (n+1)) : (gaussianReal 0 (V ij)).IsOpenPosMeasure :=
    gaussianReal_isOpenPosMeasure 0 (hV ij)
  let ν := Measure.pi (fun ij : UpperIndex (n+1) => gaussianReal 0 (V ij))
  let W := fun z : UpperIndex (n+1) → ℝ => symmetricMatrix z
  let F := fun z : UpperIndex (n+1) → ℝ => matrixAbsoluteDet n k (W z)
  let E := W ⁻¹' maximumEvent n k
  let G := E.indicator F
  have hFC : Continuous F := by
    unfold F matrixAbsoluteDet W
    exact (continuous_const.sub (symmetricMatrix_continuous (n+1))).matrix_det.abs
  have hMeasE : MeasurableSet E :=
    (maximumEvent_measurable n k).preimage (symmetricMatrix_measurable (n+1))
  have hFI : Integrable F ν := by
    have hi : Integrable (matrixAbsoluteDet n k) (goeLaw (n+1) N b) := by
      have he (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : |(A-k • 1).det|=matrixAbsoluteDet n k A := by
        unfold matrixAbsoluteDet
        rw [show A-k • 1=-(k • 1-A) by module,Matrix.det_neg,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      simpa only [he] using (fixed_shifted_determinant_integrable (n+1) N b k).abs
    change Integrable (matrixAbsoluteDet n k) (ν.map W) at hi
    exact (integrable_map_measure (matrixAbsoluteDet_measurable n k).aestronglyMeasurable
      (symmetricMatrix_measurable (n+1)).aemeasurable).mp hi
  have hGI : Integrable G ν := hFI.indicator hMeasE
  have hSym (z : UpperIndex (n+1) → ℝ) (i j : Fin (n+1)) : W z i j=W z j i := by
    change symmetricMatrix z i j=symmetricMatrix z j i
    unfold symmetricMatrix
    by_cases hij : i ≤ j
    · by_cases hji : j ≤ i
      · have heq := le_antisymm hij hji
        subst j
        rfl
      · simp [hij,hji]
    · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
      simp [hij,hji]
  have hMat : Continuous (fun z : UpperIndex (n+1) → ℝ => matrixToGaussian (W z)) := by
    unfold matrixToGaussian
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (continuous_apply j).comp ((continuous_apply i).comp (symmetricMatrix_continuous (n+1)))
  let O := {z : UpperIndex (n+1) → ℝ |
    ‖gaussianMatrixCLM (matrixToGaussian (W z))‖ < k ∧ F z ≠ 0}
  have hOpen : IsOpen O := by
    change IsOpen ({z | ‖gaussianMatrixCLM (matrixToGaussian (W z))‖ < k} ∩ Function.support F)
    have hOperator : Continuous (fun z : UpperIndex (n+1) → ℝ =>
        gaussianMatrixCLM (matrixToGaussian (W z))) :=
      (gaussianMatrixCLM_continuous (n+1)).comp hMat
    exact (isOpen_lt hOperator.norm continuous_const).inter hFC.isOpen_support
  have hOzero : (0 : UpperIndex (n+1) → ℝ) ∈ O := by
    have hz : W (0 : UpperIndex (n+1) → ℝ)=0 := by
      ext i j
      simp [W,symmetricMatrix]
    constructor
    · rw [hz]
      have hzg : matrixToGaussian (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)=0 := by ext i j;rfl
      rw [hzg,show gaussianMatrixCLM 0=0 from (gaussianMatrixToCLM (n+1)).map_zero,norm_zero]
      exact hk
    · dsimp only [F]
      rw [hz]
      simp [matrixAbsoluteDet,hk.ne']
  have hSub : O ⊆ Function.support G := by
    intro z hz
    have hEig := symmetric_eigenvalue_abs_le_opNorm (matrixToGaussian (W z)) (hSym z) (0 : Fin (n+1))
    have hE : z ∈ E := by
      exact (le_abs_self _).trans_lt (hEig.trans_lt hz.1)
    change G z ≠ 0
    dsimp only [G]
    rw [Set.indicator_of_mem hE]
    exact hz.2
  have hPos := (hOpen.measure_pos ν ⟨0,hOzero⟩).trans_le (measure_mono hSub)
  have hIntegral : 0 < ∫ z,G z ∂ν :=
    (integral_pos_iff_support_of_nonneg (fun z => Set.indicator_nonneg (fun _ _ => abs_nonneg _) z) hGI).mpr hPos
  unfold maximumMean
  rw [←integral_indicator (maximumEvent_measurable n k)]
  change 0 < ∫ A,(maximumEvent n k).indicator (matrixAbsoluteDet n k) A ∂ν.map W
  rw [integral_map (symmetricMatrix_measurable (n+1)).aemeasurable
    ((matrixAbsoluteDet_measurable n k).stronglyMeasurable.indicator (maximumEvent_measurable n k)).aestronglyMeasurable]
  exact hIntegral
end SlowEquilibration.GOEMaximumDeterminant
