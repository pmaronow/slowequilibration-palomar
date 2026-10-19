-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiniteFeatures
public import SlowEquilibration.PureTensorJetFeatures

/-! Exact Gaussian law of a normalized fixed-slot j-fold trace of the
original iid ordered tensor. Distinct free-index rows use disjoint actual
coefficient entries. Their Gram is calculated, rather than assumed. -/

@[expose] public section
namespace SlowEquilibration.OrderedTensorTraceGaussianBank
noncomputable section
open MeasureTheory ProbabilityTheory Function
open GaussianFiniteFeatures SphericalAging.FiniteModel
open scoped RealInnerProductSpace BigOperators
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The fixed trace slots consist of two identical j-tuples after the q
free slots. All coefficient coordinates are original ordered tensor entries. -/
def tracedIndex {N q j : ℕ} (a : TensorIndex N q) (b : TensorIndex N j) :
    TensorIndex N (q+j+j) := Fin.addCases (Fin.addCases a b) b

/-- Different free rows and different contracted indices are disjoint
coordinates of the original tensor. -/
theorem tracedIndex_eq_iff {N q j : ℕ} (a c : TensorIndex N q) (b d : TensorIndex N j) :
    tracedIndex a b=tracedIndex c d ↔ a=c ∧ b=d := by
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h (Fin.castAdd j (Fin.castAdd j i))
      simpa only [tracedIndex,Fin.addCases_left] using hi
    · funext i
      have hi := congrFun h (Fin.castAdd j (Fin.natAdd q i))
      simpa only [tracedIndex,Fin.addCases_left,Fin.addCases_right] using hi
  · rintro ⟨rfl,rfl⟩
    rfl

def traceNormalization (N j : ℕ) : ℝ := (Real.sqrt ((N : ℝ)^j))⁻¹

def rawTraceFeature (N q j : ℕ) (a : TensorIndex N q) :
    EuclideanSpace ℝ (TensorIndex N (q+j+j)) :=
  ∑ b : TensorIndex N j, EuclideanSpace.basisFun (TensorIndex N (q+j+j)) ℝ (tracedIndex a b)

def traceFeature (N q j : ℕ) (a : TensorIndex N q) :
    EuclideanSpace ℝ (TensorIndex N (q+j+j)) :=
  traceNormalization N j • rawTraceFeature N q j a

/-- The unnormalized Gram has exactly N^j diagonal entries per free row. -/
theorem rawTraceFeature_inner (N q j : ℕ) (a c : TensorIndex N q) :
    inner ℝ (rawTraceFeature N q j a) (rawTraceFeature N q j c)=
      if a=c then (N : ℝ)^j else 0 := by
  classical
  unfold rawTraceFeature
  simp only [sum_inner,inner_sum,
    orthonormal_iff_ite.mp (EuclideanSpace.basisFun (TensorIndex N (q+j+j)) ℝ).orthonormal,
    tracedIndex_eq_iff]
  by_cases h : a=c
  · subst c
    simp only [true_and,ite_true]
    simp [Fintype.card_fin]
  · simp [h]

/-- The actual normalized trace rows form an orthonormal coefficient bank. -/
theorem traceFeature_inner {N : ℕ} (hN : 0 < N) (q j : ℕ) (a c : TensorIndex N q) :
    inner ℝ (traceFeature N q j a) (traceFeature N q j c)=if a=c then 1 else 0 := by
  classical
  have hpow : 0 < (N : ℝ)^j := pow_pos (Nat.cast_pos.mpr hN) j
  have hunit : traceNormalization N j*traceNormalization N j*(N : ℝ)^j=1 := by
    unfold traceNormalization
    rw [←pow_two,inv_pow,Real.sq_sqrt hpow.le]
    field_simp [hpow.ne']
  unfold traceFeature
  rw [real_inner_smul_left,real_inner_smul_right,rawTraceFeature_inner]
  by_cases h : a=c
  · simp only [h,ite_true]
    simpa only [mul_assoc] using hunit
  · simp only [h,ite_false,mul_zero]

/-- The literal continuous linear map of all original coefficient entries. -/
def traceBank (N q j : ℕ) : EuclideanSpace ℝ (TensorIndex N (q+j+j)) →L[ℝ]
    EuclideanSpace ℝ (TensorIndex N q) :=
  observation (fun a => innerSL ℝ (traceFeature N q j a))

theorem traceBank_apply (N q j : ℕ) (g : EuclideanSpace ℝ (TensorIndex N (q+j+j)))
    (a : TensorIndex N q) :
    traceBank N q j g a=traceNormalization N j*∑ b : TensorIndex N j,g (tracedIndex a b) := by
  rw [traceBank,observation_apply,innerSL_apply_apply,traceFeature,real_inner_smul_left,
    rawTraceFeature,sum_inner]
  simp only [EuclideanSpace.basisFun_inner]

/-- Exact iid standard tensor Gaussian law for the normalized trace bank,
derived from the literal original coefficient Gram calculation. -/
theorem traceBank_map_stdGaussian {N : ℕ} (hN : 0 < N) (q j : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (TensorIndex N (q+j+j)))).map (traceBank N q j)=
      stdGaussian (EuclideanSpace ℝ (TensorIndex N q)) := by
  classical
  let f := fun a : TensorIndex N q => innerSL ℝ (traceFeature N q j a)
  let g := fun a : TensorIndex N q =>
    innerSL ℝ (EuclideanSpace.basisFun (TensorIndex N q) ℝ a)
  have hgram : ∀ a c,inner ℝ ((f a).adjoint 1) ((f c).adjoint 1)=
      inner ℝ ((g a).adjoint 1) ((g c).adjoint 1) := by
    intro a c
    dsimp only [f,g]
    rw [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,
      ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,
      ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,
      ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,
      traceFeature_inner hN q j]
    exact (orthonormal_iff_ite.mp (EuclideanSpace.basisFun (TensorIndex N q) ℝ).orthonormal a c).symm
  have h := observation_law_eq f g hgram
  have hid : observation g=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (TensorIndex N q)) := by
    ext z a
    change inner ℝ (EuclideanSpace.basisFun (TensorIndex N q) ℝ a) z=z a
    simp only [EuclideanSpace.basisFun_inner]
  have hmap : (stdGaussian (EuclideanSpace ℝ (TensorIndex N q))).map (observation g)=
      stdGaussian (EuclideanSpace ℝ (TensorIndex N q)) := by
    rw [hid]
    change (stdGaussian (EuclideanSpace ℝ (TensorIndex N q))).map id=_
    rw [Measure.map_id]
  exact h.trans hmap

def tensorFlatten {N p : ℕ} (J : SphericalAging.FiniteModel.Disorder N p) :
    EuclideanSpace ℝ (TensorIndex N p) := WithLp.toLp 2 J

def orderedTensorTrace (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) :
    EuclideanSpace ℝ (TensorIndex N q) := traceBank N q j (tensorFlatten J)

theorem orderedTensorTrace_apply (N q j : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (a : TensorIndex N q) :
    orderedTensorTrace N q j J a=(Real.sqrt ((N : ℝ)^j))⁻¹*
      ∑ b : TensorIndex N j,J (tracedIndex a b) := by
  rw [orderedTensorTrace,traceBank_apply]
  rfl

/-- The bank is a standard iid q-tensor under the original actual product
disorder law; no substituted law or Gaussian-bank premise is used. -/
theorem actual_orderedTensorTrace_hasLaw {N : ℕ} (hN : 0 < N) (q j : ℕ) :
    HasLaw (orderedTensorTrace N q j) (stdGaussian (EuclideanSpace ℝ (TensorIndex N q)))
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := by
  have hm : Measurable (tensorFlatten (N := N) (p := q+j+j)) :=
    (PiLp.continuous_toLp 2 _).measurable
  have hflat : (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).map tensorFlatten=
      stdGaussian (EuclideanSpace ℝ (TensorIndex N (q+j+j))) := by
    exact map_pi_eq_stdGaussian
  refine ⟨((traceBank N q j).continuous.measurable.comp hm).aemeasurable,?_⟩
  change (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).map
    ((traceBank N q j) ∘ tensorFlatten)=_
  rw [←Measure.map_map (traceBank N q j).continuous.measurable hm,hflat,
    traceBank_map_stdGaussian hN q j]

end
end SlowEquilibration.OrderedTensorTraceGaussianBank
