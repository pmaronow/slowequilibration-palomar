-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeOriginalMeanBound
public import SlowEquilibration.SphericalLatitudeCorrectionBankMeasurable

/-! Actual original-disorder event for uniform latitude tangent means.
All degree and bank constants are fixed from the actual mixture before
choosing dimension. No conditional mean bound is assumed. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalLatitudeTensorMoments
open scoped ENNReal RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Model-only upper bound for the literal entire higher correction. -/
def originalLatitudeCorrectionConstant (μ : FiniteMixture) : ℝ :=
  ∑ p : Degree μ.maxDegree,Real.sqrt (mixtureCoefficients μ p)*latitudeCorrectionUniformConstant p.val.val

def originalLatitudeBankCount (μ : FiniteMixture) : ℕ :=
  ∑ p : Degree μ.maxDegree,latitudeCorrectionBankCount p.val.val

/-- One true original seed event controls every physical axis and latitude. -/
def originalLatitudeMeanGood (n : ℕ) (μ : FiniteMixture) : Set (Disorder (n+1) μ.maxDegree) :=
  regularDisorder∩{J | ∀ p : Degree μ.maxDegree,J p∉latitudeCorrectionBadBanks n p.val.val}

theorem originalLatitudeMeanGood_measurable {n : ℕ} (hn : 1≤n) (μ : FiniteMixture) :
    MeasurableSet (originalLatitudeMeanGood n μ) := by
  apply (regularDisorder_measurable _ _).inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro p
  exact ((latitudeCorrectionBadBanks_measurable hn).preimage (measurable_pi_apply p)).compl

/-- True Gaussian exceptional probability of the actual shared seed event. -/
theorem originalLatitudeMeanGood_failure_probability {n : ℕ} (hn : 1≤n) (μ : FiniteMixture) :
    disorderLaw (n+1) μ.maxDegree (originalLatitudeMeanGood n μ)ᶜ≤
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)))+
        (originalLatitudeBankCount μ : ℝ≥0∞)*ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
  have he : (originalLatitudeMeanGood n μ)ᶜ=(regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ∪
      ⋃ p : Degree μ.maxDegree,{J : Disorder (n+1) μ.maxDegree | J p∈latitudeCorrectionBadBanks n p.val.val} := by
    ext J
    simp only [originalLatitudeMeanGood,Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_ofPred_eq,
      Set.mem_union,Set.mem_iUnion,not_and_or,not_forall,not_not]
  rw [he]
  apply (measure_union_le _ _).trans
  apply add_le_add
  · have h := regularDisorder_failure_probability (N := n+1) (P := μ.maxDegree) (by omega)
    have h' := ENNReal.ofReal_le_ofReal h
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using h'
  · apply (measure_iUnion_fintype_le _ _).trans
    calc
      _≤∑ p : Degree μ.maxDegree,(latitudeCorrectionBankCount p.val.val : ℝ≥0∞)*
          ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
        apply Finset.sum_le_sum
        intro p hp
        have heq : disorderLaw (n+1) μ.maxDegree {J | J p∈latitudeCorrectionBadBanks n p.val.val}=
            SphericalAging.FiniteModel.disorderLaw (n+1) p.val.val (latitudeCorrectionBadBanks n p.val.val) := by
          convert (degree_block_hasLaw p).measure_eq (latitudeCorrectionBadBanks_measurable hn) using 1
          all_goals congr 1
        rw [heq]
        exact latitudeCorrectionBadBanks_probability hn
      _=_ := by rw [←Finset.sum_mul];simp only [originalLatitudeBankCount,Nat.cast_sum]

/-- Literal entire higher correction is dimension-uniform on the true event. -/
theorem originalLatitudeCorrectionEnvelope_le_on_good {n : ℕ} (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ) :
    originalLatitudeCorrectionEnvelope n μ J≤originalLatitudeCorrectionConstant μ := by
  unfold originalLatitudeCorrectionEnvelope originalLatitudeCorrectionConstant
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (latitudeCorrectionEnvelope_le_of_not_badBanks (J p) (hJ.2 p))
    (Real.sqrt_nonneg _)

/-- Actual uniform original latitude tangent mean at the true minimum
supported degree, with all constants selected before dimension. -/
theorem actual_original_latitudeObservableMean_uniform_bound {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (mixtureCoefficients μ) J u (latitudeFrameAt u) r|≤
      originalLatitudeLeadingConstant μ*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        originalLatitudeCorrectionConstant μ :=
  (actual_original_latitudeObservableMean_abs_le hn μ J hJ.1 u hu hr).trans
    (add_le_add le_rfl (originalLatitudeCorrectionEnvelope_le_on_good μ J hJ))

end
end SlowEquilibration.EntranceLatitudeTangentObservable
