module
public import QuantitativePaper.VectorTerminalSmooth
public import QuantitativePaper.SmoothGaussianStep

@[expose] public section

/-! Genuine joint C∞ regularity of the finite-dimensional Parisi recursion.
For every finite derivative order the positive-order jets have a global bound
independent of the disorder and field evaluation point. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

def vectorJointShift (n : ℕ) (c : ℝ) : Field n →L[ℝ] VectorParameter n :=
  (0 : Field n →L[ℝ] (Couplings n × ℝ)).prod
    (Real.sqrt c • ContinuousLinearMap.id ℝ (Field n))

theorem vectorJointShift_add (n : ℕ) (c : ℝ) (p : VectorParameter n) (z : Field n) :
    p+vectorJointShift n c z = (p.1,fieldShift c p.2 z) := by
  ext
  · simp [vectorJointShift]
  · simp [vectorJointShift]
  · rfl

theorem gaussianShiftColeHopf_vectorRecursion {n k : ℕ} (s : RSBScheme k) (β t c m : ℝ)
    (j : ℕ) (p : VectorParameter n) :
    gaussianShiftColeHopf (vectorJointShift n c) m
      (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) p =
      vectorColeHopfStep c m (vectorRecursion s β t p.1 j) p.2 := by
  unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition vectorColeHopfStep vectorStepPartition
  simp_rw [vectorJointShift_add]

theorem vectorRecursion_joint_smooth_bounded_jets {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (N j : ℕ) :
    ContDiff ℝ N (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) ∧
    ∃ K : ℝ,1 ≤ K ∧ ∀ i,1 ≤ i → i ≤ N → ∀ x : VectorParameter n,
      ‖iteratedFDeriv ℝ i (fun p => vectorRecursion s β t p.1 j p.2) x‖ ≤ K^i := by
  induction j with
  | zero => exact ⟨contDiff_vectorTerminalPotential_joint n β t N,
      exists_vectorTerminalPotential_joint_jet_bound n β t N⟩
  | succ j ih =>
    obtain ⟨hSmooth,K,hK,hJets⟩ := ih
    let c := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let m := s.m (k+1-j)
    have hh := gaussianShiftColeHopf_smooth_bounded_jets N
      (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) hSmooth
      (vectorJointLipschitzConstant n β t) (vectorRecursion_joint_lipschitz s β t j)
      K hK hJets (vectorJointShift n c) m
    have he : gaussianShiftColeHopf (vectorJointShift n c) m
        (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) =
        fun p : VectorParameter n => vectorRecursion s β t p.1 (j+1) p.2 := by
      funext p
      exact gaussianShiftColeHopf_vectorRecursion s β t c m j p
    rw [he] at hh
    exact hh

theorem contDiff_vectorRecursion_joint {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) :=
  contDiff_infty.mpr (fun N => (vectorRecursion_joint_smooth_bounded_jets s β t N j).1)

theorem exists_vectorRecursion_joint_jet_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (N j : ℕ) : ∃ K : ℝ,1 ≤ K ∧ ∀ i,1 ≤ i → i ≤ N → ∀ x : VectorParameter n,
      ‖iteratedFDeriv ℝ i (fun p => vectorRecursion s β t p.1 j p.2) x‖ ≤ K^i :=
  (vectorRecursion_joint_smooth_bounded_jets s β t N j).2

end QuantitativePaper
