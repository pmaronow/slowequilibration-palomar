module
public import QuantitativePaper.ExponentialJetBounds
public import QuantitativePaper.VectorColeHopf

@[expose] public section

/-! Actual Gaussian parameter smoothing preserves higher regularity. Local
dominating functions are constructed from the Gaussian exponential moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianShiftPartition {n : ℕ} (A : Field n →L[ℝ] E) (m : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z,Real.exp (m*f (x+A z)) ∂fieldGaussian n

theorem gaussian_shift_abs_le {n : ℕ} (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (A : Field n →L[ℝ] E) (x y : E) (z : Field n) (hy : dist y x < 1) :
    |f (y+A z)| ≤ |f x|+(L : ℝ)*(1+‖A‖*‖z‖) := by
  have hd : dist (y+A z) x ≤ 1+‖A‖*‖z‖ := by
    calc
      dist (y+A z) x ≤ dist y x+‖A z‖ := by
        rw [dist_eq_norm,dist_eq_norm]
        convert norm_add_le (y-x) (A z) using 1 <;> congr 1 <;> abel
      _ ≤ _ := add_le_add hy.le (A.le_opNorm z)
  have hff := hf.dist_le_mul (y+A z) x
  rw [Real.dist_eq] at hff
  calc
    |f (y+A z)| ≤ |f x|+|f (y+A z)-f x| := by
      convert abs_add_le (f x) (f (y+A z)-f x) using 1 <;> congr 1 <;> ring
    _ ≤ |f x|+(L : ℝ)*dist (y+A z) x := add_le_add (le_refl _) hff
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hd L.coe_nonneg)

def gaussianJetCoefficient (m K : ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ)*(max 1 |m|)^j*K^j

theorem gaussianJetCoefficient_nonneg (m K : ℝ) (hK : 0 ≤ K) (j : ℕ) :
    0 ≤ gaussianJetCoefficient m K j := by unfold gaussianJetCoefficient;positivity

theorem gaussianShiftPartition_smooth_inputs {n : ℕ} (N : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ j,1 ≤ j → j ≤ N → ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (A : Field n →L[ℝ] E) (m : ℝ) :
    (∀ z,ContDiff ℝ N (fun x => Real.exp (m*f (x+A z)))) ∧
    (∀ j,j ≤ N → ∀ x,AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => Real.exp (m*f (y+A z))) x) (fieldGaussian n)) ∧
    (∀ x,∃ s ∈ 𝓝 x,∃ B : ℕ → Field n → ℝ,
      (∀ j,j ≤ N → Integrable (B j) (fieldGaussian n)) ∧
      ∀ j,j ≤ N → ∀ y ∈ s,∀ z,
        ‖iteratedFDeriv ℝ j (fun u => Real.exp (m*f (u+A z))) y‖ ≤ B j z) := by
  let F := fun x => Real.exp (m*f x)
  have hF : ContDiff ℝ N F := (contDiff_const.mul hf).exp
  refine ⟨fun z => hF.comp (contDiff_id.add contDiff_const),?_,?_⟩
  · intro j hj x
    change AEStronglyMeasurable (fun z => iteratedFDeriv ℝ j (fun y => F (y+A z)) x) _
    simp_rw [iteratedFDeriv_comp_add_right]
    exact ((hF.continuous_iteratedFDeriv (by norm_cast)).comp
      (continuous_const.add A.continuous)).aestronglyMeasurable
  · intro x
    let B : ℕ → Field n → ℝ := fun j z => gaussianJetCoefficient m K j*
      Real.exp (|m| * (|f x|+(L : ℝ)))*Real.exp (|m| *(L : ℝ)*‖A‖*‖z‖)
    refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),B,?_,?_⟩
    · intro j hj
      exact (SYK.integrable_exp_mul_norm (ι := Fin n) (|m| *(L : ℝ)*‖A‖)).const_mul
        (gaussianJetCoefficient m K j*Real.exp (|m| * (|f x|+(L : ℝ))))
    · intro j hj y hy z
      have hjets' (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
          ‖iteratedFDeriv ℝ i f (y+A z)‖ ≤ K^i := hjets i hi (hij.trans hj) _
      have hnorm := norm_iteratedFDeriv_exp_mul_le f hf hj m K (y+A z) hjets'
      change ‖iteratedFDeriv ℝ j (fun u => F (u+A z)) y‖ ≤ _
      rw [iteratedFDeriv_comp_add_right]
      have hdom : Real.exp (m*f (y+A z)) ≤
          Real.exp (|m| * (|f x|+(L : ℝ)))*Real.exp (|m| *(L : ℝ)*‖A‖*‖z‖) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        calc
          m*f (y+A z) ≤ |m| * |f (y+A z)| := by rw [← abs_mul];exact le_abs_self _
          _ ≤ |m| * (|f x|+(L : ℝ)*(1+‖A‖*‖z‖)) :=
            mul_le_mul_of_nonneg_left (gaussian_shift_abs_le f L hlip A x y z hy) (abs_nonneg m)
          _ = _ := by ring
      change ‖iteratedFDeriv ℝ j F (y+A z)‖ ≤ _
      apply hnorm.trans
      unfold B gaussianJetCoefficient
      have hh := mul_le_mul_of_nonneg_left hdom (gaussianJetCoefficient_nonneg m K hK j)
      simpa only [gaussianJetCoefficient,mul_assoc,mul_left_comm,mul_comm] using hh

theorem contDiff_gaussianShiftPartition {n : ℕ} (N : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ j,1 ≤ j → j ≤ N → ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (A : Field n →L[ℝ] E) (m : ℝ) : ContDiff ℝ N (gaussianShiftPartition A m f) := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianShiftPartition_smooth_inputs N f hf L hlip K hK hjets A m
  exact contDiff_integral_of_dominated_derivatives N (fieldGaussian n) _ h₁ h₂ h₃

theorem integrable_gaussianShiftPartition_input {n : ℕ} (f : E → ℝ) (L : ℝ≥0)
    (hlip : LipschitzWith L f) (A : Field n →L[ℝ] E) (m : ℝ) (x : E) :
    Integrable (fun z => Real.exp (m*f (x+A z))) (fieldGaussian n) := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianShiftPartition_smooth_inputs 0 f
    (show ContDiff ℝ (0 : ℕ) f from by simpa using (contDiff_zero.mpr hlip.continuous : ContDiff ℝ 0 f)) L hlip 1 zero_le_one
    (fun j hj hj0 => by omega) A m
  obtain ⟨s,hs,B,hBi,hB⟩ := h₃ x
  apply (hBi 0 (le_refl _)).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul
      (hlip.continuous.comp (continuous_const.add A.continuous))))).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      simpa only [norm_iteratedFDeriv_zero] using hB 0 (le_refl _) x (mem_of_mem_nhds hs) z

theorem gaussianShiftPartition_pos {n : ℕ} (f : E → ℝ) (L : ℝ≥0)
    (hlip : LipschitzWith L f) (A : Field n →L[ℝ] E) (m : ℝ) (x : E) :
    0 < gaussianShiftPartition A m f x := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    (integrable_gaussianShiftPartition_input f L hlip A m x)).mpr
  have he : Function.support (fun z => Real.exp (m*f (x+A z))) = univ := by
    ext z
    simp [Function.mem_support,Real.exp_ne_zero]
  rw [he]
  simp

theorem norm_iteratedFDeriv_gaussianShiftPartition_le {n : ℕ} (N j : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (A : Field n →L[ℝ] E) (m : ℝ) (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (gaussianShiftPartition A m f) x‖ ≤
      gaussianJetCoefficient m K j*gaussianShiftPartition A m f x := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianShiftPartition_smooth_inputs N f hf L hlip K hK hjets A m
  rw [show iteratedFDeriv ℝ j (gaussianShiftPartition A m f) x =
      ∫ z,iteratedFDeriv ℝ j (fun y => Real.exp (m*f (y+A z))) x ∂fieldGaussian n from
    iteratedFDeriv_integral_of_dominated_derivatives N (fieldGaussian n) _ h₁ h₂ h₃ j hj x]
  have hb := norm_integral_le_of_norm_le
    ((integrable_gaussianShiftPartition_input f L hlip A m x).const_mul (gaussianJetCoefficient m K j))
    (f := fun z => iteratedFDeriv ℝ j (fun y => Real.exp (m*f (y+A z))) x)
    (Eventually.of_forall fun z => by
      change ‖iteratedFDeriv ℝ j (fun y => (fun u => Real.exp (m*f u)) (y+A z)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_right (f := fun u => Real.exp (m*f u)) j (A z) x]
      have hh := norm_iteratedFDeriv_exp_mul_le f hf hj m K (x+A z)
        (fun i hi hij => hjets i hi (hij.trans hj) _)
      simpa only [gaussianJetCoefficient,mul_assoc,mul_left_comm,mul_comm] using hh)
  rw [integral_const_mul] at hb
  exact hb

end QuantitativePaper
