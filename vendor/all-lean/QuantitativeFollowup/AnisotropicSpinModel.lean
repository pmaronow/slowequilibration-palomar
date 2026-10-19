module
public import QuantitativePaper.VectorTerminalLinear
public import FourPapersCommon.FiniteStateCascadeGrowth

@[expose] public section

/-! The literal independent Gaussian coupling model and positive diagonal
auxiliary covariance of the follow-up posterior lemma. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open QuantitativePaper FourPapersCommon
open scoped BigOperators NNReal
namespace QuantitativeFollowup

abbrev AnisotropicCouplingIndex (n : ℕ) := {ij : Fin n×Fin n // ij.1 ≤ ij.2}
abbrev AnisotropicDisorder (n : ℕ) := EuclideanSpace ℝ (AnisotropicCouplingIndex n)
abbrev AnisotropicParameterIndex (n : ℕ) := AnisotropicCouplingIndex n⊕Fin n
abbrev AnisotropicParameter (n : ℕ) := EuclideanSpace ℝ (AnisotropicParameterIndex n)

structure AnisotropicSpinModel (n : ℕ) where
  variance : Fin n→ℝ
  variance_pos : ∀i,0 < variance i
  coupling : AnisotropicCouplingIndex n→ℝ

def anisotropicDisorderLaw (n : ℕ) : Measure (AnisotropicDisorder n) :=
  stdGaussian (AnisotropicDisorder n)

instance anisotropicDisorderLaw_probability (n : ℕ) : IsProbabilityMeasure (anisotropicDisorderLaw n) := by
  unfold anisotropicDisorderLaw
  infer_instance

def anisotropicParameterPoint {n : ℕ} (ω : AnisotropicDisorder n) (x : Field n) : AnisotropicParameter n :=
  WithLp.toLp 2 (fun j=>Sum.elim (fun i=>ω i) (fun i=>x i) j)

def anisotropicTerminalLinear {n : ℕ} (D : AnisotropicSpinModel n) (σ : Configuration n) :
    AnisotropicParameter n→L[ℝ]ℝ :=
  (∑e : AnisotropicCouplingIndex n,
    (D.coupling e*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) • EuclideanSpace.proj (Sum.inl e))+
  ∑i : Fin n,Paper.spinSign (σ i) • EuclideanSpace.proj (Sum.inr i)

def anisotropicHamiltonian {n : ℕ} (D : AnisotropicSpinModel n)
    (ω : AnisotropicDisorder n) (x : Field n) (σ : Configuration n) : ℝ :=
  (∑e : AnisotropicCouplingIndex n,D.coupling e*ω e*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))+
    fieldDot x σ

theorem anisotropicTerminalLinear_apply {n : ℕ} (D : AnisotropicSpinModel n)
    (ω : AnisotropicDisorder n) (x : Field n) (σ : Configuration n) :
    anisotropicTerminalLinear D σ (anisotropicParameterPoint ω x)=anisotropicHamiltonian D ω x σ := by
  simp only [anisotropicTerminalLinear,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,anisotropicHamiltonian,fieldDot]
  change (∑e : AnisotropicCouplingIndex n,
    D.coupling e*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)*ω e)+
    (∑i : Fin n,Paper.spinSign (σ i)*x i)=_
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

def anisotropicNoiseMap {n : ℕ} (D : AnisotropicSpinModel n) : Field n→L[ℝ]Field n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun z=>WithLp.toLp 2 (fun i=>Real.sqrt (D.variance i)*z i)
      map_add':=by intro x y;ext i;simp only [PiLp.add_apply,mul_add]
      map_smul':=by intro c x;ext i;simp only [PiLp.smul_apply,smul_eq_mul,RingHom.id_apply];ring }

@[simp] theorem anisotropicNoiseMap_apply {n : ℕ} (D : AnisotropicSpinModel n) (z : Field n) (i : Fin n) :
    anisotropicNoiseMap D z i=Real.sqrt (D.variance i)*z i := rfl

theorem anisotropicNoiseMap_inner {n : ℕ} (D : AnisotropicSpinModel n) (x y : Field n) :
    inner ℝ (anisotropicNoiseMap D x) (anisotropicNoiseMap D y)=∑i : Fin n,D.variance i*x i*y i := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,anisotropicNoiseMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=(Real.sqrt (D.variance i))^2*x i*y i := by ring
    _=D.variance i*x i*y i := by rw [Real.sq_sqrt (D.variance_pos i).le]

def anisotropicFieldInjection (n : ℕ) : Field n→L[ℝ]AnisotropicParameter n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun z=>WithLp.toLp 2 (Sum.elim (fun _=>0) (fun i=>z i))
      map_add':=by intro x y;ext i;cases i <;> simp
      map_smul':=by intro c x;ext i;cases i <;> simp }

theorem anisotropicFieldInjection_apply {n : ℕ} (x : Field n) :
    anisotropicFieldInjection n x=anisotropicParameterPoint 0 x := rfl

end QuantitativeFollowup
