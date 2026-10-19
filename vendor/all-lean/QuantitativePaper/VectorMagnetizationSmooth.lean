module
public import QuantitativePaper.VectorPosteriorJets
public import QuantitativePaper.BoundedJets

@[expose] public section

/-! The actual magnetization is the field derivative of the genuine joint
vector potential. Every coordinate is bounded and has bounded jets of all
orders, including after the actual Gaussian-history coordinate map. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def vectorJointCoordinateDirection (n : ℕ) (i : Fin n) : VectorParameter n :=
  (0,EuclideanSpace.single i 1)

theorem vectorMagnetization_component_eq_fderiv {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) (p : VectorParameter n) (i : Fin n) :
    vectorMagnetization s β t p.1 j p.2 i=
      fderiv ℝ (fun q : VectorParameter n => vectorRecursion s β t q.1 j q.2) p
        (vectorJointCoordinateDirection n i) := by
  let F := fun q : VectorParameter n => vectorRecursion s β t q.1 j q.2
  have hd := hasDerivAt_on_affine_line F
    ((contDiff_vectorRecursion_joint s β t j).of_le (by simp)) p (vectorJointCoordinateDirection n i) 0
  have he : (fun r : ℝ => F (p+r • vectorJointCoordinateDirection n i))=
      fun r => vectorRecursion s β t p.1 j (p.2+r • EuclideanSpace.single i 1) := by
    funext r
    have he' : p+r • vectorJointCoordinateDirection n i=
        (p.1,p.2+r • EuclideanSpace.single i 1) := by
      apply Prod.ext
      · simp [vectorJointCoordinateDirection]
      · rfl
    rw [he']
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_vectorRecursion_coordinate s β t p.1 j p.2 i)
  simpa using hh.symm

theorem boundedPositiveJets_vectorRecursion_joint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) :
    BoundedPositiveJets (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) := by
  refine ⟨contDiff_vectorRecursion_joint s β t j,?_⟩
  intro N hN
  obtain ⟨K,hK,hBound⟩ := exists_vectorRecursion_joint_jet_bound s β t N j
  exact ⟨K^N,pow_nonneg (by linarith) _,fun x => hBound N hN le_rfl x⟩

theorem boundedJets_vectorMagnetization_component {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) (i : Fin n) :
    BoundedJets (fun p : VectorParameter n => vectorMagnetization s β t p.1 j p.2 i) := by
  have he : (fun p : VectorParameter n => vectorMagnetization s β t p.1 j p.2 i)=
      fun p => fderiv ℝ (fun q : VectorParameter n => vectorRecursion s β t q.1 j q.2) p
        (vectorJointCoordinateDirection n i) :=
    funext fun p => vectorMagnetization_component_eq_fderiv s β t j p i
  have hf := (boundedPositiveJets_vectorRecursion_joint s β t j).fderiv_apply
    (vectorJointCoordinateDirection n i)
  rw [←he] at hf
  apply hf.boundedJets 1 (by norm_num)
  intro p
  rw [Real.norm_eq_abs]
  exact vectorMagnetization_component_bound s β t p.1 j p.2 i

def vectorEuclideanMagnetization {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (z : VectorGaussianSpace n k) : Field n :=
  vectorMagnetization s β t (vectorEuclideanStateLinear s β t i z).1 (k+2-i)
    (vectorEuclideanStateLinear s β t i z).2

theorem boundedJets_vectorEuclideanMagnetization_component {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (l : Fin n) :
    BoundedJets (fun z : VectorGaussianSpace n k => vectorEuclideanMagnetization s β t i z l) :=
  (boundedJets_vectorMagnetization_component s β t (k+2-i) l).comp_linear
    (vectorEuclideanStateLinear s β t i)

end QuantitativePaper
