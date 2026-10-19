module

public import OverlapPaper.PhysicalArrays
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

@[expose] public section

/-! Measurable finite Gram realizations for the Dovbysh–Sudakov construction.
The vectors are columns of the unique positive square root, so there is no
unproved measurable choice of eigenvectors. This module is a finite
foundation, not a directing-measure representation theorem. -/
noncomputable section
open Set Filter Matrix WithLp
open scoped Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def finiteGramVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) := toLp 2 (fun j => CFC.sqrt A j i)

theorem finiteGramVector_inner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (i j : Fin n) :
    ⟪finiteGramVector A i,finiteGramVector A j⟫ = A i j := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hsq : (CFC.sqrt A)ᴴ*CFC.sqrt A = A := by
    rw [hs,←sq,CFC.sq_sqrt A hA.nonneg]
  calc
    _ = ((CFC.sqrt A)ᴴ*CFC.sqrt A) i j := by
      simp only [finiteGramVector,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
        Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = A i j := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hsq

theorem finiteGramVector_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hdiag : ∀ i,A i i = 1) (i : Fin n) :
    ‖finiteGramVector A i‖ = 1 := by
  have hh := finiteGramVector_inner A hA i i
  rw [real_inner_self_eq_norm_sq,hdiag] at hh
  nlinarith [norm_nonneg (finiteGramVector A i)]

theorem continuousOn_finiteGramVector {n : ℕ} (i : Fin n) :
    ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => finiteGramVector A i)
      {A | A.PosSemidef} := by
  have hc : ContinuousOn (CFC.sqrt : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      {A | A.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ))
  have hcol : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ =>
      (toLp 2 (fun j => A j i) : EuclideanSpace ℝ (Fin n))) := by fun_prop
  exact hcol.comp_continuousOn hc

abbrev GramArray := {R : OverlapArray // R ∈ GramArrays}

def principalGramVector (n : ℕ) (R : GramArray) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  finiteGramVector (principalMatrix R.1 n) i

theorem principalGramVector_inner (n : ℕ) (R : GramArray) (i j : Fin n) :
    ⟪principalGramVector n R i,principalGramVector n R j⟫ =
      completeArray R.1 i j :=
  finiteGramVector_inner _ (R.2 n) i j

theorem principalGramVector_norm (n : ℕ) (R : GramArray) (i : Fin n) :
    ‖principalGramVector n R i‖ = 1 := by
  apply finiteGramVector_norm _ (R.2 n) _ i
  intro j
  simp [principalMatrix,completeArray]

theorem continuous_principalGramVector (n : ℕ) (i : Fin n) :
    Continuous (fun R : GramArray => principalGramVector n R i) := by
  exact (continuousOn_finiteGramVector i).comp_continuous
    ((continuous_principalMatrix n).comp continuous_subtype_val) (fun R => R.2 n)

theorem measurable_principalGramVector (n : ℕ) (i : Fin n) :
    Measurable (fun R : GramArray => principalGramVector n R i) :=
  (continuous_principalGramVector n i).measurable

end OverlapPaper
