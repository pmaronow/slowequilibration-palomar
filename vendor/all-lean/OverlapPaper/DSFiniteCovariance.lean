module

public import OverlapPaper.DSPrincipalSpectrum

@[expose] public section

/-! The empirical covariance and its exact two-sample tail identity. This
connects spectral square tails to the L² error in off-diagonal Gram entries. -/
noncomputable section
open Set Filter Matrix WithLp
open scoped Topology BigOperators RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 800000

def finiteEmpiricalCovariance {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun k l => (n:ℝ)⁻¹*∑ i,v i k*v i l)

theorem finiteEmpiricalCovariance_posSemidef {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) : (finiteEmpiricalCovariance v).PosSemidef := by
  have he : finiteEmpiricalCovariance v = (n:ℝ)⁻¹ •
      ∑ i : Fin n,Matrix.vecMulVec (fun k => v i k) (fun k => v i k) := by
    ext k l
    simp only [finiteEmpiricalCovariance,Matrix.of_apply,Matrix.smul_apply,Matrix.sum_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  rw [he]
  apply Matrix.PosSemidef.smul _ (by positivity : 0 ≤ (n:ℝ)⁻¹)
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun k => v i k)

theorem finiteEmpiricalCovariance_trace_le_one {n d : ℕ} (hn : 0 < n)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i,‖v i‖ ≤ 1) :
    (finiteEmpiricalCovariance v).trace ≤ 1 := by
  have he : (finiteEmpiricalCovariance v).trace = (n:ℝ)⁻¹*∑ i,‖v i‖^2 := by
    simp only [Matrix.trace,Matrix.diag_apply,finiteEmpiricalCovariance,Matrix.of_apply]
    rw [←Finset.mul_sum,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [←real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [he]
  calc
    _ ≤ (n:ℝ)⁻¹*∑ _ : Fin n,(1:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hv i,norm_nonneg (v i)]
    _ = 1 := by simp [hnR.ne']

theorem sum_four_comm {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → ι → κ → κ → ℝ) :
    (∑ i ∈ s,∑ j ∈ s,∑ k ∈ t,∑ l ∈ t,f i j k l) =
      ∑ k ∈ t,∑ l ∈ t,∑ i ∈ s,∑ j ∈ s,f i j k l := by
  calc
    _ = ∑ i ∈ s,∑ k ∈ t,∑ j ∈ s,∑ l ∈ t,f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k ∈ t,∑ i ∈ s,∑ j ∈ s,∑ l ∈ t,f i j k l := Finset.sum_comm
    _ = ∑ k ∈ t,∑ i ∈ s,∑ l ∈ t,∑ j ∈ s,f i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

theorem finite_tail_pair_square_sum {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (s : Finset (Fin d)) :
    (∑ i : Fin n,∑ j : Fin n,(∑ k ∈ s,v i k*v j k)^2) =
      ∑ k ∈ s,∑ l ∈ s,(∑ i : Fin n,v i k*v i l)^2 := by
  have he (i j : Fin n) : (∑ k ∈ s,v i k*v j k)^2 =
      ∑ k ∈ s,∑ l ∈ s,(v i k*v i l)*(v j k*v j l) := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_two,Finset.sum_mul_sum]

/-- Two independent samples from the finite empirical measure have a Gram
tail error whose mean square is the covariance tail's Frobenius square. -/
theorem finite_empirical_tail_identity {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (s : Finset (Fin d)) :
    (n:ℝ)⁻¹^2*(∑ i : Fin n,∑ j : Fin n,(∑ k ∈ s,v i k*v j k)^2) =
      ∑ k ∈ s,∑ l ∈ s,(finiteEmpiricalCovariance v k l)^2 := by
  rw [finite_tail_pair_square_sum]
  simp only [finiteEmpiricalCovariance,Matrix.of_apply,mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.mul_sum _ _ _

end OverlapPaper
