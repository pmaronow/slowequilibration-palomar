-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPhysicalResidualContinuousField
public import SlowEquilibration.SphericalParisiGroundPrimalUpper
public import SlowEquilibration.SphericalParisiContinuousMaximum

/-! Canonical actual finite mixtures as aggregate ordered Gaussian tensor
fields, with exact covariance derivatives, whole continuous-field law and
physical maximum normalization. The true HS upper is invoked internally. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiFiniteMixtureGroundBridge
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTaylorRemainder SphericalCriticalLatitude
open FiniteTensorMixtureMaximum PureTensorJetBounds GaussianContinuousFieldLaw
open SphericalParisiLabeledCovariance SphericalParisiPositivePolynomialCalculus
open SphericalParisiGroundRSUpper SphericalParisiGroundPrimalUpper
open SphericalParisiContinuousMaximum LatitudeGroundTrial
open scoped Topology BigOperators RealInnerProductSpace
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def tensorDegree (μ : FiniteMixture) (p : Degree μ.maxDegree) : ℕ := p.val.val

def tensorCoefficient (μ : FiniteMixture) : Degree μ.maxDegree→ℝ := mixtureCoefficients μ

theorem tensorDegree_ge_two (μ : FiniteMixture) (p : Degree μ.maxDegree) : 2 ≤ tensorDegree μ p := p.property

theorem tensorCoefficient_nonnegative (μ : FiniteMixture) : ∀ p,0 ≤ tensorCoefficient μ p :=
  mixtureCoefficients_nonnegative μ

theorem tensorXi_eq (μ : FiniteMixture) (r : ℝ) : xi (tensorDegree μ) (tensorCoefficient μ) r=μ.xi r :=
  covariancePolynomial_mixture μ r

theorem tensorXi1_eq (μ : FiniteMixture) (r : ℝ) : xi1 (tensorDegree μ) (tensorCoefficient μ) r=μ.xi1 r := by
  have hfun : xi (tensorDegree μ) (tensorCoefficient μ)=μ.xi := funext (tensorXi_eq μ)
  have H := xi_hasDerivAt (tensorDegree μ) (tensorCoefficient μ) r
  rw [hfun] at H
  exact H.unique (μ.hasDerivAt_xi r)

theorem tensorXi2_eq (μ : FiniteMixture) (r : ℝ) : xi2 (tensorDegree μ) (tensorCoefficient μ) r=μ.xi2 r := by
  have hfun : xi1 (tensorDegree μ) (tensorCoefficient μ)=μ.xi1 := funext (tensorXi1_eq μ)
  have H := xi1_hasDerivAt (tensorDegree μ) (tensorCoefficient μ) r
  rw [hfun] at H
  exact H.unique (μ.hasDerivAt_xi1 r)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The literal aggregate iid ordered-tensor continuous field, retaining
the exact physical sqrt(N/d) scale and canonical mixture coefficients. -/
def finiteMixtureTensorContinuousField (μ : FiniteMixture) (N d : ℕ)
    (x : K→Vector d) (hx : Continuous x) :
    EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ))→L[ℝ] C(K,ℝ) :=
  featureContinuousField
    (fun v => innerSL ℝ (Real.sqrt ((N : ℝ)/(d : ℝ)) • feature (tensorDegree μ) (tensorCoefficient μ) (x v)))
    (fun _g => ((((feature_continuous (tensorDegree μ) (tensorCoefficient μ)).comp hx).const_smul
      (Real.sqrt ((N : ℝ)/(d : ℝ)))).inner continuous_const))

omit [CompactSpace K] in
theorem finiteMixtureTensorContinuousField_covariance (μ : FiniteMixture) (N d : ℕ) (hd : 0 < d)
    (x : K→Vector d) (hx : Continuous x) (v w : K) :
    cov[fun g => finiteMixtureTensorContinuousField μ N d x hx g v,
      fun g => finiteMixtureTensorContinuousField μ N d x hx g w;
      stdGaussian (EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ)))]=
      (N : ℝ)*μ.xi (inner ℝ (x v) (x w)) := by
  classical
  rw [evaluation_covariance]
  change (innerSL ℝ (Real.sqrt ((N : ℝ)/(d : ℝ)) • feature (tensorDegree μ) (tensorCoefficient μ) (x v)))
    ((innerSL ℝ (Real.sqrt ((N : ℝ)/(d : ℝ)) • feature (tensorDegree μ) (tensorCoefficient μ) (x w))).adjoint 1)=_
  rw [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,
    innerSL_apply_apply,real_inner_smul_left,real_inner_smul_right,
    feature_inner _ _ (tensorCoefficient_nonnegative μ)]
  have hsum := tensorXi_eq μ (inner ℝ (x v) (x w))
  change (∑ i,tensorCoefficient μ i*(inner ℝ (x v) (x w))^tensorDegree μ i)=
    μ.xi (inner ℝ (x v) (x w)) at hsum
  rw [hsum]
  have hs : 0 ≤ (N : ℝ)/(d : ℝ) := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)
  calc
    _=(Real.sqrt ((N : ℝ)/(d : ℝ)))^2*(d : ℝ)*μ.xi (inner ℝ (x v) (x w)) := by ring
    _=_ := by rw [Real.sq_sqrt hs];field_simp [Nat.cast_ne_zero.mpr hd.ne']

/-- Genuine full C(K)-law equality, proved from the actual evaluation
covariances of the physical residual field and literal aggregate tensor model. -/
theorem physicalResidualContinuousField_tensor_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (μ : FiniteMixture) (N d : ℕ) (hd : 0 < d) (x : K→Vector d) (hx : Continuous x) :
    (stdGaussian (EuclideanDisorder d μ.maxDegree)).map (physicalResidualContinuousField μ N d x hx)=
      (stdGaussian (EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ)))).map
        (finiteMixtureTensorContinuousField μ N d x hx) := by
  apply continuous_field_law_eq_of_covariance
  intro v w
  rw [physicalResidualContinuousField_covariance μ N d hd,
    finiteMixtureTensorContinuousField_covariance μ N d hd]

theorem finiteMixtureTensorContinuousField_maximum (μ : FiniteMixture) (N d : ℕ) (hd : 0 < d)
    (g : EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ))) :
    maximum (finiteMixtureTensorContinuousField μ N d (fun x : UnitSphere d => x.val) continuous_subtype_val g)=
      Real.sqrt ((N : ℝ)/(d : ℝ))*actualMaximum (N := d) (tensorDegree μ) (tensorCoefficient μ) g := by
  let : NeZero d := ⟨hd.ne'⟩
  let f : C(UnitSphere d,ℝ) :=
    ⟨fun x => inner ℝ (feature (tensorDegree μ) (tensorCoefficient μ) x.val) g,
      (((feature_continuous _ _).comp continuous_subtype_val).inner continuous_const)⟩
  have he : finiteMixtureTensorContinuousField μ N d (fun x : UnitSphere d => x.val) continuous_subtype_val g=
      Real.sqrt ((N : ℝ)/(d : ℝ)) • f := by
    ext x
    simp only [finiteMixtureTensorContinuousField,featureContinuousField_apply,innerSL_apply_apply,
      real_inner_smul_left,ContinuousMap.smul_apply,smul_eq_mul]
    rfl
  rw [he,maximum_nonneg_smul f (Real.sqrt_nonneg _)]
  rfl

/-- Exact actual Gaussian expected-maximum transport, with both genuine
coefficient laws and the physical sqrt(N/d) compensation visible. -/
theorem physicalResidualContinuousField_expected_maximum (μ : FiniteMixture) (N d : ℕ) (hd : 0 < d) :
    (∫ g,maximum (physicalResidualContinuousField μ N d
      (fun x : UnitSphere d => x.val) continuous_subtype_val g) ∂stdGaussian (EuclideanDisorder d μ.maxDegree))=
      Real.sqrt ((N : ℝ)/(d : ℝ))*
        (∫ g,actualMaximum (N := d) (tensorDegree μ) (tensorCoefficient μ) g
          ∂SYK.standardGaussianMeasureOnEuclidean
            (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ))) := by
  let : NeZero d := ⟨hd.ne'⟩
  let X := physicalResidualContinuousField μ N d (fun x : UnitSphere d => x.val) continuous_subtype_val
  let Y := finiteMixtureTensorContinuousField μ N d (fun x : UnitSphere d => x.val) continuous_subtype_val
  have hLaw := physicalResidualContinuousField_tensor_law μ N d hd
    (fun x : UnitSphere d => x.val) continuous_subtype_val
  have H := maximum_integral_eq_of_field_law _ _ X Y X.continuous.measurable Y.continuous.measurable hLaw
  rw [integral_congr_ae (.of_forall (finiteMixtureTensorContinuousField_maximum μ N d hd)),integral_const_mul] at H
  have hG : stdGaussian (EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ)))=
      SYK.standardGaussianMeasureOnEuclidean (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ)) := by
    rw [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
  rw [hG] at H
  exact H

theorem finiteMixture_functional_nonnegative (μ : FiniteMixture) {L α s : ℝ}
    (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) :
    0 ≤ functional μ.xi1 μ.xi2 L α s := by
  have H := literal_functional_nonnegative (tensorDegree μ) (tensorCoefficient μ)
    (tensorCoefficient_nonnegative μ) hα hs hb
  rw [funext (tensorXi1_eq μ),funext (tensorXi2_eq μ)] at H
  exact H

/-- Every actual canonical finite mixture satisfies the literal HS trial
upper by the proved original Gaussian pressure/REM/net argument. -/
theorem eventual_finiteMixture_ground_functional_upper (μ : FiniteMixture) {L α s : ℝ}
    (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop,
      (∫ g,actualMaximum (N := d) (tensorDegree μ) (tensorCoefficient μ) g
        ∂SYK.standardGaussianMeasureOnEuclidean
          (FiniteTensorMixtureMaximum.Coordinate d (tensorDegree μ)))/(d : ℝ) ≤
      functional μ.xi1 μ.xi2 L α s+ε := by
  have H := eventual_actual_ground_functional_upper_all_degrees (tensorDegree μ) (tensorCoefficient μ)
    (tensorCoefficient_nonnegative μ) hα hs hb hε
  rw [funext (tensorXi1_eq μ),funext (tensorXi2_eq μ)] at H
  exact H

/-- The physical N=n+1 versus transverse d=n normalization is derived
for the actual finite mixture field, with no expected-maximum premise. -/
theorem eventual_physical_finiteMixture_ground_upper (μ : FiniteMixture) {L α s : ℝ}
    (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∫ g,maximum (physicalResidualContinuousField μ (n+1) n
        (fun x : UnitSphere n => x.val) continuous_subtype_val g)
          ∂stdGaussian (EuclideanDisorder n μ.maxDegree))/((n+1 : ℕ) : ℝ) ≤
        functional μ.xi1 μ.xi2 L α s+ε := by
  have hMean := eventual_finiteMixture_ground_functional_upper μ hα hs hb hε
  have hR : 0 ≤ functional μ.xi1 μ.xi2 L α s+ε :=
    add_nonneg (finiteMixture_functional_nonnegative μ hα hs hb) hε.le
  filter_upwards [hMean,eventually_gt_atTop (0 : ℕ)] with n hM hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNR : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (by omega)
  rw [physicalResidualContinuousField_expected_maximum μ (n+1) n hn]
  have hBound := (div_le_iff₀ hnR).mp hM
  have hRatio : 1 ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    push_cast
    linarith
  have hSqrt : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ))*(n : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
    have hRatio0 : 0 ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ) := le_trans zero_le_one hRatio
    have hRoot : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)) ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) hRatio0).mp
      rw [Real.sq_sqrt hRatio0]
      nlinarith [sq_nonneg ((((n+1 : ℕ) : ℝ)/(n : ℝ))-1)]
    have H := mul_le_mul_of_nonneg_right hRoot hnR.le
    simpa only [div_mul_cancel₀ _ hnR.ne'] using H
  apply (div_le_iff₀ hNR).mpr
  calc
    _ ≤ Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ))*
        ((functional μ.xi1 μ.xi2 L α s+ε)*(n : ℝ)) :=
      mul_le_mul_of_nonneg_left hBound (Real.sqrt_nonneg _)
    _ ≤ (functional μ.xi1 μ.xi2 L α s+ε)*((n+1 : ℕ) : ℝ) := by
      have H := mul_le_mul_of_nonneg_left hSqrt hR
      convert H using 1
      ring

end SlowEquilibration.SphericalParisiFiniteMixtureGroundBridge
