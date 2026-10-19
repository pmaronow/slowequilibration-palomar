module

public import OverlapPaper.DSFiniteCovariance

@[expose] public section

/-! Orthogonal rotations preserve every finite Gram entry and expose the
actual rotated empirical covariance. These identities permit measurable
approximate spectral rotations without altering the array law. -/
noncomputable section
open Set Filter Matrix WithLp
open scoped Topology MatrixOrder Matrix.Norms.L2Operator BigOperators RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 800000

def rotatedGramMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  star (U : Matrix (Fin n) (Fin n) ℝ)*CFC.sqrt A

def rotatedGramVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun j => rotatedGramMatrix A U j i)

theorem rotatedGramMatrix_star_mul_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (U : Matrix.unitaryGroup (Fin n) ℝ) :
    star (rotatedGramMatrix A U)*rotatedGramMatrix A U = A := by
  have hU : (U : Matrix (Fin n) (Fin n) ℝ)*star (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).star_eq
  unfold rotatedGramMatrix
  rw [star_mul,star_star,hS]
  calc
    _ = CFC.sqrt A*((U : Matrix (Fin n) (Fin n) ℝ)*
        star (U : Matrix (Fin n) (Fin n) ℝ))*CFC.sqrt A := by simp only [mul_assoc]
    _ = A := by rw [hU,mul_one,←sq,CFC.sq_sqrt A hA.nonneg]

theorem rotatedGramVector_inner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (U : Matrix.unitaryGroup (Fin n) ℝ) (i j : Fin n) :
    ⟪rotatedGramVector A U i,rotatedGramVector A U j⟫ = A i j := by
  calc
    _ = (star (rotatedGramMatrix A U)*rotatedGramMatrix A U) i j := by
      simp only [rotatedGramVector,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
        Matrix.mul_apply,Matrix.star_apply,star_trivial]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := congrArg (fun P : Matrix (Fin n) (Fin n) ℝ => P i j)
      (rotatedGramMatrix_star_mul_self A hA U)

theorem rotatedGramVector_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hdiag : ∀ i,A i i = 1)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (i : Fin n) : ‖rotatedGramVector A U i‖ = 1 := by
  have hh := rotatedGramVector_inner A hA U i i
  rw [real_inner_self_eq_norm_sq,hdiag] at hh
  nlinarith [norm_nonneg (rotatedGramVector A U i)]

theorem rotatedGramVector_covariance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (U : Matrix.unitaryGroup (Fin n) ℝ) :
    finiteEmpiricalCovariance (rotatedGramVector A U) =
      (n:ℝ)⁻¹ • (star (U : Matrix (Fin n) (Fin n) ℝ)*A*(U : Matrix (Fin n) (Fin n) ℝ)) := by
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).star_eq
  have he : finiteEmpiricalCovariance (rotatedGramVector A U) =
      (n:ℝ)⁻¹ • (rotatedGramMatrix A U*star (rotatedGramMatrix A U)) := by
    ext k l
    simp only [finiteEmpiricalCovariance,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_apply,Matrix.star_apply,star_trivial,rotatedGramVector]
  rw [he]
  congr 1
  unfold rotatedGramMatrix
  rw [star_mul,star_star,hS]
  calc
    _ = star (U : Matrix (Fin n) (Fin n) ℝ)*(CFC.sqrt A*CFC.sqrt A)*
        (U : Matrix (Fin n) (Fin n) ℝ) := by simp only [mul_assoc]
    _ = _ := by rw [←sq,CFC.sq_sqrt A hA.nonneg]

end OverlapPaper
