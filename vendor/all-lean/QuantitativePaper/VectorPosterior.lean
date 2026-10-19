module
public import QuantitativePaper.VectorDensityExponent
public import QuantitativePaper.VectorCoordinateSmooth
public import QuantitativePaper.VectorSmooth
public import FourPapersCommon.GaussianLebesgueDensity

@[expose] public section

/-! The actual vector posterior density relative to Lebesgue volume and counting
measure. The potential retains the root floor coefficient and every free-mass
increment, and is genuinely C∞. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000

def vectorEuclideanHistoryPotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorGaussianSpace n k) : ℝ :=
  vectorHistoryPotential s β t (vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z)) i

def vectorEuclideanTerminalExponent {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) (z : VectorGaussianSpace n k) : ℝ :=
  vectorTerminalExponent n β t
    (vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z) (Fin.last (k+2))).1
    (vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z) (Fin.last (k+2))).2 σ

def vectorPosteriorPotential {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (σ : Configuration n) (z : VectorGaussianSpace n k) : ℝ :=
  standardGaussianPotential z-vectorEuclideanTerminalExponent s β t σ z+
    (s.m 1-a)*vectorEuclideanHistoryPotential s β t 1 z+
    (∑ i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*vectorEuclideanHistoryPotential s β t (i+2) z)+
    Real.log (vectorOuterPartition (n := n) s β t a)

theorem contDiff_vectorEuclideanHistoryPotential {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) : ContDiff ℝ ∞ (vectorEuclideanHistoryPotential (n := n) s β t i) := by
  have hh := (contDiff_apply ℝ (VectorState n) (Fin.ofNat (k+3) i)).comp
    (contDiff_vectorEuclideanHistory (n := n) s β t ∞)
  exact (contDiff_vectorRecursion_joint (n := n) s β t (k+2-i)).comp hh

theorem contDiff_vectorEuclideanTerminalExponent {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (σ : Configuration n) :
    ContDiff ℝ ∞ (vectorEuclideanTerminalExponent (n := n) s β t σ) := by
  have hh := (contDiff_apply ℝ (VectorState n) (Fin.last (k+2))).comp
    (contDiff_vectorEuclideanHistory (n := n) s β t ∞)
  have he : vectorEuclideanTerminalExponent (n := n) s β t σ =
      (vectorTerminalLinear n β t σ) ∘
        (fun z => vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z) (Fin.last (k+2))) := by
    funext z
    exact (vectorTerminalLinear_apply n β t σ _).symm
  rw [he]
  exact (vectorTerminalLinear n β t σ).contDiff.comp hh

theorem contDiff_standardGaussianPotential {ι : Type*} [Fintype ι] :
    ContDiff ℝ ∞ (standardGaussianPotential (ι := ι)) := by
  have he : standardGaussianPotential (ι := ι) = fun x : EuclideanSpace ℝ ι =>
      inner ℝ x x/2+(Fintype.card ι : ℝ)*Real.log (Real.sqrt (2*Real.pi)) := by
    funext x
    simp [standardGaussianPotential,real_inner_self_eq_norm_sq]
  rw [he]
  exact ((ContDiff.inner ℝ contDiff_id contDiff_id).div_const 2).add contDiff_const

theorem contDiff_vectorPosteriorPotential {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (σ : Configuration n) : ContDiff ℝ ∞ (vectorPosteriorPotential (n := n) s β t a σ) := by
  unfold vectorPosteriorPotential
  exact (((contDiff_standardGaussianPotential.sub (contDiff_vectorEuclideanTerminalExponent s β t σ)).add
    (contDiff_const.mul (contDiff_vectorEuclideanHistoryPotential s β t 1))).add
    (ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_vectorEuclideanHistoryPotential s β t (i+2))))).add
    contDiff_const

theorem vectorEuclideanDensity_eq_posterior {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (hq : s.q 1=0) (z : VectorGaussianSpace n k) (σ : Configuration n) :
    vectorEuclideanDensity s β t a (z,σ) = ENNReal.ofReal
      (Real.exp (standardGaussianPotential z-vectorPosteriorPotential s β t a σ z)) := by
  change vectorCoordinateDensity s β t a (vectorEuclideanCoordinates n k z,σ)=_
  rw [vectorCoordinateDensity_eq_floor_exp s β t a hq]
  unfold vectorPosteriorPotential vectorEuclideanHistoryPotential vectorEuclideanTerminalExponent
  congr 2
  ring

theorem vectorEuclideanJointLaw_eq_Lebesgue_posterior {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) :
    vectorEuclideanJointLaw (n := n) s β t a =
      ((volume : Measure (VectorGaussianSpace n k)).prod
        (Measure.count : Measure (Configuration n))).withDensity
        (fun p => ENNReal.ofReal (Real.exp (-vectorPosteriorPotential s β t a p.2 p.1))) := by
  have hg : Measurable (fun z : VectorGaussianSpace n k =>
      ENNReal.ofReal (Real.exp (-standardGaussianPotential z))) :=
    (Real.continuous_exp.comp contDiff_standardGaussianPotential.continuous.neg).measurable.ennreal_ofReal
  have hg' : Measurable (fun p : VectorGaussianSpace n k × Configuration n =>
      ENNReal.ofReal (Real.exp (-standardGaussianPotential p.1))) := hg.comp measurable_fst
  rw [vectorEuclideanJointLaw,standardGaussianEuclidean_eq_expDensity,prod_withDensity_left hg]
  rw [←withDensity_mul _ hg' (measurable_vectorEuclideanDensity s β t a)]
  apply withDensity_congr_ae
  filter_upwards [] with p
  rcases p with ⟨z,σ⟩
  simp only [Pi.mul_apply]
  rw [vectorEuclideanDensity_eq_posterior s β t a hq,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  ring

end QuantitativePaper
