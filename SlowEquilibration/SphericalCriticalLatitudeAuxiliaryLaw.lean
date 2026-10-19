-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeSourceTau
public import SlowEquilibration.FiniteTensorMixtureMaximum

/-! The actual critical-conditioned latitude process has the full continuous
law of a concrete iid ordered-tensor field with source covariance tau_r.
Degree zero and degree one are retained as their own independent coefficient
blocks. The model and its coefficients are fixed before the dimension. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open SphericalTwoPointCovariance SphericalParisiConditionedLatitudeCovariance
open GaussianContinuousFieldLaw SphericalForm
open scoped RealInnerProductSpace BigOperators
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The extra zero-degree block is separate from the actual nonconstant
support. This includes the source linear coefficient whenever it is nonzero. -/
abbrev SourceAuxiliaryIndex (μ : FiniteMixture) (Q r : ℝ) :=
  Option ↑(sourceNonconstantCoefficients μ Q r).support

def sourceAuxiliaryDegree (μ : FiniteMixture) (Q r : ℝ) :
    SourceAuxiliaryIndex μ Q r → ℕ
  | none => 0
  | some j => j.val

def sourceAuxiliaryCoefficient (μ : FiniteMixture) (Q r : ℝ) :
    SourceAuxiliaryIndex μ Q r → ℝ
  | none => sourceTau μ Q r 0
  | some j => sourceNonconstantCoefficients μ Q r j.val

/-- The source degree-one term is retained without alteration. -/
theorem source_nonconstant_linear_coefficient_eq (μ : FiniteMixture) (Q r : ℝ) :
    sourceNonconstantCoefficients μ Q r 1=sourceLinearCoefficient μ Q r := by
  rw [sourceNonconstantCoefficients,Finsupp.add_apply,Finsupp.single_eq_same,
    μ.taylorResidualCoefficients_zero_below_two _ _ (k := 1) (by norm_num),add_zero]

/-- Every block apart from the explicitly adjoined constant has positive
degree, including the actual possible degree-one block. -/
theorem source_auxiliary_nonconstant_degree_pos (μ : FiniteMixture) (Q r : ℝ)
    (j : ↑(sourceNonconstantCoefficients μ Q r).support) :
    1 ≤ sourceAuxiliaryDegree μ Q r (some j) := by
  have hj := Finsupp.mem_support_iff.mp j.property
  have hn : j.val≠0 := by
    intro hzero
    rw [hzero,sourceNonconstantCoefficients_zero] at hj
    exact hj rfl
  exact Nat.one_le_iff_ne_zero.mpr hn

theorem sourceAuxiliaryCoefficient_nonneg (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    (j : SourceAuxiliaryIndex μ Q r) : 0 ≤ sourceAuxiliaryCoefficient μ Q r j := by
  cases j with
  | none => exact sourceTau_zero_nonneg μ hQ hnp r
  | some j => exact sourceNonconstantCoefficients_nonneg μ hQ ⟨hr.1.le,hr.2.le⟩ j.val

/-- The concrete ordered-tensor covariance polynomial is literally tau_r,
including its actual constant and possible linear terms. -/
theorem sourceAuxiliaryPolynomial_eq_tau (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) (t : ℝ) :
    (∑ j : SourceAuxiliaryIndex μ Q r,
      sourceAuxiliaryCoefficient μ Q r j*t^(sourceAuxiliaryDegree μ Q r j))=
      sourceTau μ Q r t := by
  classical
  rw [Fintype.sum_option]
  simp only [sourceAuxiliaryCoefficient,sourceAuxiliaryDegree,pow_zero,mul_one]
  rw [Finset.sum_coe_sort (s := (sourceNonconstantCoefficients μ Q r).support)
    (f := fun j => sourceNonconstantCoefficients μ Q r j*t^j)]
  change sourceTau μ Q r 0+(sourceNonconstantCoefficients μ Q r).sum
    (fun j a => a*t^j)=_
  rw [source_nonconstant_polynomial_eq μ hQ hr t]
  ring

/-- Literal latitude map with a unit transverse parameter. -/
def sourceUnitLatitudeMap {N d : ℕ} (u : Vector N)
    (e : Vector d →ₗᵢ[ℝ] Vector N) (r : ℝ) (x : Vector d) : Vector N :=
  r • u+Real.sqrt ((N : ℝ)*(1-r^2)) • e x

theorem sourceUnitLatitudeMap_continuous {N d : ℕ} (u : Vector N)
    (e : Vector d →ₗᵢ[ℝ] Vector N) (r : ℝ) :
    Continuous (sourceUnitLatitudeMap u e r) := by
  unfold sourceUnitLatitudeMap
  have hc := (continuous_const : Continuous (fun _ : Vector d => r • u)).add
    (e.continuous.const_smul (Real.sqrt ((N : ℝ)*(1-r^2))))
  exact hc.congr (fun _ => rfl)

theorem sourceUnitLatitudeMap_overlap {N d : ℕ} (hN : 0 < N)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ x,inner ℝ (e x) u=0)
    (r : ℝ) (x : Vector d) : overlap u (sourceUnitLatitudeMap u e r x)=r := by
  have he' : inner ℝ u (e x)=0 := by rw [real_inner_comm];exact he x
  simp only [sourceUnitLatitudeMap,overlap,inner_add_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hu,he',mul_zero,add_zero]
  exact mul_div_cancel_right₀ r (Nat.cast_ne_zero.mpr hN.ne')

/-- Exact geometry of two literal latitude parameters, before applying the
actual posterior covariance theorem. -/
theorem sourceUnitLatitudeMap_pair_overlap {N d : ℕ} (hN : 0 < N)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ x,inner ℝ (e x) u=0)
    {r : ℝ} (hr : r∈Ioo (0 : ℝ) 1) (x y : Vector d) :
    overlap (sourceUnitLatitudeMap u e r x) (sourceUnitLatitudeMap u e r y)=
      r^2+(1-r^2)*inner ℝ x y := by
  have hs : 0 ≤ (N : ℝ)*(1-r^2) :=
    mul_nonneg (Nat.cast_nonneg N) (by nlinarith [hr.1,hr.2])
  have he' : inner ℝ u (e y)=0 := by rw [real_inner_comm];exact he y
  have hinner : inner ℝ (sourceUnitLatitudeMap u e r x) (sourceUnitLatitudeMap u e r y)=
      (N : ℝ)*(r^2+(1-r^2)*inner ℝ x y) := by
    simp only [sourceUnitLatitudeMap,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,he x,he',real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,hu,e.inner_map_map,
      mul_zero,add_zero,zero_add]
    calc
      _=r^2*(N : ℝ)+(Real.sqrt ((N : ℝ)*(1-r^2)))^2*inner ℝ x y := by ring
      _=_ := by rw [Real.sq_sqrt hs];ring
  unfold overlap
  rw [hinner]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')

/-- Unit transverse parameters map to the actual physical sphere. -/
theorem sourceUnitLatitudeMap_norm_sq {N d : ℕ} (hN : 0 < N)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ x,inner ℝ (e x) u=0)
    {r : ℝ} (hr : r∈Ioo (0 : ℝ) 1) (x : Vector d) (hx : ‖x‖^2=1) :
    ‖sourceUnitLatitudeMap u e r x‖^2=(N : ℝ) := by
  have ho : overlap (sourceUnitLatitudeMap u e r x) (sourceUnitLatitudeMap u e r x)=1 := by
    rw [sourceUnitLatitudeMap_pair_overlap hN u hu e he hr x x,
      real_inner_self_eq_norm_sq,hx]
    ring
  unfold overlap at ho
  rw [real_inner_self_eq_norm_sq] at ho
  simpa only [one_mul] using (div_eq_iff (Nat.cast_ne_zero.mpr hN.ne')).mp ho

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The concrete independent ordered-tensor auxiliary continuous field.
Its physical sqrt(N/d) factor is displayed, with its model fixed first. -/
def auxiliaryContinuousField (μ : FiniteMixture) (Q r : ℝ) (N d : ℕ)
    (x : K → Vector d) (hx : Continuous x) :
    EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate d (sourceAuxiliaryDegree μ Q r))
      →L[ℝ] C(K,ℝ) :=
  featureContinuousField
    (fun v => innerSL ℝ (Real.sqrt ((N : ℝ)/(d : ℝ)) •
      FiniteTensorMixtureMaximum.feature (sourceAuxiliaryDegree μ Q r)
        (sourceAuxiliaryCoefficient μ Q r) (x v)))
    (fun _g => ((((FiniteTensorMixtureMaximum.feature_continuous
      (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r)).comp hx).const_smul
        (Real.sqrt ((N : ℝ)/(d : ℝ)))).inner continuous_const))

omit [CompactSpace K] in
/-- Every evaluation covariance of the concrete iid auxiliary tensor field
is exactly the source polynomial with the correct physical N prefactor. -/
theorem auxiliaryContinuousField_covariance (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    (N d : ℕ) (hd : 0 < d) (x : K → Vector d) (hx : Continuous x) (v w : K) :
    cov[fun g => auxiliaryContinuousField μ Q r N d x hx g v,
      fun g => auxiliaryContinuousField μ Q r N d x hx g w;
      stdGaussian (EuclideanSpace ℝ
        (FiniteTensorMixtureMaximum.Coordinate d (sourceAuxiliaryDegree μ Q r)))]=
      (N : ℝ)*sourceTau μ Q r (inner ℝ (x v) (x w)) := by
  classical
  rw [evaluation_covariance]
  change (innerSL ℝ (Real.sqrt ((N : ℝ)/(d : ℝ)) •
      FiniteTensorMixtureMaximum.feature (sourceAuxiliaryDegree μ Q r)
        (sourceAuxiliaryCoefficient μ Q r) (x v)))
    ((innerSL ℝ (Real.sqrt ((N : ℝ)/(d : ℝ)) •
      FiniteTensorMixtureMaximum.feature (sourceAuxiliaryDegree μ Q r)
        (sourceAuxiliaryCoefficient μ Q r) (x w))).adjoint 1)=_
  rw [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,
    innerSL_apply_apply,real_inner_smul_left,real_inner_smul_right,
    FiniteTensorMixtureMaximum.feature_inner _ _ (sourceAuxiliaryCoefficient_nonneg μ hQ hnp hr),
    sourceAuxiliaryPolynomial_eq_tau μ hQ hr]
  have hs : 0 ≤ (N : ℝ)/(d : ℝ) := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)
  calc
    _=(Real.sqrt ((N : ℝ)/(d : ℝ)))^2*(d : ℝ)*sourceTau μ Q r (inner ℝ (x v) (x w)) := by ring
    _=_ := by rw [Real.sq_sqrt hs];field_simp [Nat.cast_ne_zero.mpr hd.ne']

/-- Exact full continuous-process transport from the actual source
critical-point posterior to a concrete finite iid auxiliary tensor model. -/
theorem actual_critical_latitude_auxiliary_continuous_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (μ : FiniteMixture) {Q r : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (hr : r∈Ioo (0 : ℝ) 1) (n d : ℕ) (hd : 0 < d)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (e : Vector d →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    (x : K → Vector d) (hx : Continuous x) (e₀ k₀ : ℝ) :
    let z := fun v => sourceUnitLatitudeMap u e r (x v)
    let hz : Continuous z := (sourceUnitLatitudeMap_continuous u e r).comp hx
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
      (scorePairEquiv (e₀,k₀))).map
        (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
          ContinuousMap.const K ((n+1 : ℕ)*sourceConditionalMean μ Q e₀ k₀ r))=
      (stdGaussian (EuclideanSpace ℝ
        (FiniteTensorMixtureMaximum.Coordinate d (sourceAuxiliaryDegree μ Q r)))).map
        (auxiliaryContinuousField μ Q r (n+1) d x hx) := by
  dsimp only
  let z := fun v => sourceUnitLatitudeMap u e r (x v)
  have hz : Continuous z := (sourceUnitLatitudeMap_continuous u e r).comp hx
  have hMean : criticalContinuousMean n μ Q u z hz (scorePairEquiv (e₀,k₀))=
      ContinuousMap.const K ((n+1 : ℕ)*sourceConditionalMean μ Q e₀ k₀ r) := by
    ext v
    rw [criticalContinuousMean_eq_source n μ hQ hnp u hu z hz,
      sourceUnitLatitudeMap_overlap (by omega) u hu e he]
    rfl
  rw [←hMean,actual_critical_centered_continuous_law n μ hQ hnp u hu z hz]
  apply continuous_field_law_eq_of_covariance
  intro v w
  rw [actual_critical_continuous_covariance_eq_sourceTau n μ hQ hnp u hu z hz v w
    (sourceUnitLatitudeMap_overlap (by omega) u hu e he r (x v))
    (sourceUnitLatitudeMap_overlap (by omega) u hu e he r (x w))
    (sourceUnitLatitudeMap_pair_overlap (by omega) u hu e he hr (x v) (x w)),
    auxiliaryContinuousField_covariance μ hQ hnp hr (n+1) d hd x hx v w]

end
end SlowEquilibration.SphericalCriticalLatitude
