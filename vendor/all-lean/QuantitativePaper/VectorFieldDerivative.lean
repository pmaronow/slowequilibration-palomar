module
public import QuantitativePaper.VectorMagnetizationSmooth
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

@[expose] public section

/-! Literal field derivatives of the vector potential and retained
magnetization, rather than abstract response vectors. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem vectorJointFieldDirection_sum {n : ℕ} (w : Field n) :
    ((0,w) : VectorParameter n)=∑ i : Fin n,w i • vectorJointCoordinateDirection n i := by
  apply Prod.ext
  · simp [vectorJointCoordinateDirection,Prod.fst_sum]
  · apply PiLp.ext
    intro l
    simp [vectorJointCoordinateDirection,Prod.snd_sum,Pi.single_apply]

theorem fderiv_vectorRecursion_field {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) (p : VectorParameter n) (w : Field n) :
    fderiv ℝ (fun q : VectorParameter n => vectorRecursion s β t q.1 j q.2) p (0,w)=
      inner ℝ (vectorMagnetization s β t p.1 j p.2) w := by
  rw [vectorJointFieldDirection_sum,map_sum]
  simp_rw [map_smul,←vectorMagnetization_component_eq_fderiv,smul_eq_mul]
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem contDiff_vectorEuclideanMagnetization {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) : ContDiff ℝ ∞ (vectorEuclideanMagnetization (n := n) s β t i) :=
  contDiff_piLp' 2 (fun l => (boundedJets_vectorEuclideanMagnetization_component s β t i l).1)

end QuantitativePaper
