module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The strict Schur-complement estimate needed for a quadratic tilt.
The inverse is represented by its actual linear equation, so the lemma
applies equally to a matrix inverse or a continuous linear equivalence. -/
noncomputable section
namespace QuantitativeFollowup

theorem strict_bilinear_block_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (v z : E) (τ r δ K m : ℝ)
    (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hA : ∀ w, r*‖w‖^2 ≤ A w w)
    (hAs : ∀ w₁ w₂, A w₁ w₂ = A w₂ w₁)
    (hv : ‖v‖ ≤ K) (hmr : 2*m ≤ r) (hmδ : m*(2*K^2+1) ≤ δ) :
    m*(‖z‖^2+τ^2) ≤ A z z-2*τ*A v z+τ^2*(A v v+δ) := by
  have hnorm : ‖z‖^2 ≤ 2*‖z-τ • v‖^2+2*τ^2*K^2 := by
    have ht := norm_add_le (z-τ • v) (τ • v)
    have heq : z-τ • v+τ • v=z := by abel
    rw [heq,norm_smul,Real.norm_eq_abs] at ht
    have hv' : |τ| * ‖v‖ ≤ |τ| * K := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    have htri : ‖z‖ ≤ ‖z-τ • v‖+|τ| * K := ht.trans (by linarith)
    have habs : |τ|^2=τ^2 := sq_abs τ
    have hsq := sq_nonneg (‖z-τ • v‖-|τ| * K)
    have hle := mul_le_mul htri htri (norm_nonneg z)
      (by positivity : 0 ≤ ‖z-τ • v‖+|τ| * K)
    nlinarith [norm_nonneg (z-τ • v)]
  have hscaled := mul_le_mul_of_nonneg_left hnorm hm
  have hfirst := mul_le_mul_of_nonneg_right hmr (sq_nonneg ‖z-τ • v‖)
  have hsecond := mul_le_mul_of_nonneg_right hmδ (sq_nonneg τ)
  have hform := hA (z-τ • v)
  simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul] at hform
  rw [hAs z v] at hform
  nlinarith

theorem strict_hessian_block_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) (v z : E) (τ r δ K m : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hA : ∀ w, r*‖w‖^2 ≤ inner ℝ w (A w))
    (hAs : ∀ w₁ w₂, inner ℝ w₁ (A w₂) = inner ℝ w₂ (A w₁))
    (hv : ‖v‖ ≤ K) (hmr : 2*m ≤ r) (hmδ : m*(2*K^2+1) ≤ δ) :
    m*(‖z‖^2+τ^2) ≤ inner ℝ z (A z)-2*τ*inner ℝ v (A z)+
      τ^2*(inner ℝ v (A v)+δ) := by
  have hnorm : ‖z‖^2 ≤ 2*‖z-τ • v‖^2+2*τ^2*K^2 := by
    have ht := norm_add_le (z-τ • v) (τ • v)
    have heq : z-τ • v+τ • v=z := by abel
    rw [heq,norm_smul,Real.norm_eq_abs] at ht
    have hv' : |τ| * ‖v‖ ≤ |τ| * K := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    have htri : ‖z‖ ≤ ‖z-τ • v‖+|τ| * K := ht.trans (by linarith)
    have habs : |τ|^2=τ^2 := sq_abs τ
    have hsq := sq_nonneg (‖z-τ • v‖-|τ| * K)
    have hle := mul_le_mul htri htri (norm_nonneg z)
      (by positivity : 0 ≤ ‖z-τ • v‖+|τ| * K)
    nlinarith [norm_nonneg (z-τ • v)]
  have hscaled := mul_le_mul_of_nonneg_left hnorm hm
  have hfirst := mul_le_mul_of_nonneg_right hmr (sq_nonneg ‖z-τ • v‖)
  have hsecond := mul_le_mul_of_nonneg_right hmδ (sq_nonneg τ)
  have hform := hA (z-τ • v)
  simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right] at hform
  rw [hAs z v] at hform
  nlinarith

theorem exists_strict_hessian_block_bound (r δ K : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hK : 0 ≤ K) :
    ∃ m>0, 2*m ≤ r ∧ m*(2*K^2+1) ≤ δ := by
  refine ⟨min (r/2) (δ/(2*K^2+1)),lt_min (by positivity) (by positivity),?_,?_⟩
  · have hh := min_le_left (r/2) (δ/(2*K^2+1))
    linarith
  · exact (le_div_iff₀ (by positivity : 0<2*K^2+1)).mp
      (min_le_right (r/2) (δ/(2*K^2+1)))

end QuantitativeFollowup
