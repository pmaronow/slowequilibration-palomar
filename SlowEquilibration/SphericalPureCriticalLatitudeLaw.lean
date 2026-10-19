-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalValueCriticalLatitudeCovariance
public import SlowEquilibration.SphericalPhysicalResidualContinuousField
public import SlowEquilibration.SphericalParisiPureLatitudeCovariance

/-! Actual proper-pure source10.12 latitude law. Value and zero tangent
gradient are conditioned through their genuine nonredundant posterior;
the centered process is the actual finite Taylor-residual mixture, with
zero constant and linear terms and the physical sqrt(N/d) normalization. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalTaylorRemainder
open SphericalMarkedWindows SphericalParisiPureLatitudeCovariance GaussianContinuousFieldLaw
open scoped RealInnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pure latitude residual model is fixed before the dimensions. -/
def pureLatitudeResidual (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q r : ℝ} (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) : FiniteMixture :=
  (FiniteMixture.pure p hp c hc).taylorResidual
    (mul_pos hQ (sq_pos_of_pos hr.1))
    (mul_pos hQ (show 0 < 1-r^2 by nlinarith [hr.1,hr.2]))

theorem pure_center_value_ratio (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    (FiniteMixture.pure p hp c hc).xi (Q*r)/(FiniteMixture.pure p hp c hc).xi Q=r^p := by
  rw [FiniteMixture.pure_xi,FiniteMixture.pure_xi,mul_pow]
  field_simp [hc.ne',hQ.ne']

/-- Actual proper-pure coefficient covariance with the redundant radial
observation omitted throughout. -/
theorem actual_pure_critical_residual_kernel (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q r : ℝ} (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) (n : ℕ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) (w₁ w₂ : Vector (n+1)) {t : ℝ}
    (hr₁ : overlap u w₁=r) (hr₂ : overlap u w₂=r)
    (hρ : overlap w₁ w₂=r^2+(1-r^2)*t) :
    let μ := FiniteMixture.pure p hp c hc
    let a := centerCoefficients (mixtureCoefficients μ) Q
    (valueObservation a w₁).comp (valueCriticalCoefficientResidual n μ Q u)
      (((valueObservation a w₂).comp (valueCriticalCoefficientResidual n μ Q u)).adjoint 1)=
      (n+1 : ℕ)*(pureLatitudeResidual p hp c hc hQ hr).xi t := by
  dsimp only
  rw [actual_value_critical_residual_kernel n (FiniteMixture.pure p hp c hc) hQ u hu w₁ w₂ hr₁ hr₂ hρ]
  change (n+1 : ℕ)*sourceValueTau (FiniteMixture.pure p hp c hc) Q r t=_
  rw [pure_valueTau_eq_residual_xi p hp c hc hQ hr t]
  rfl

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- The actual proper-pure conditional mean is the literal N e r^p. -/
theorem actual_pure_criticalContinuousMean (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (n : ℕ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (e : ℝ) (v : K) {r : ℝ}
    (hr : overlap u (z v)=r) :
    valueCriticalContinuousMean n (FiniteMixture.pure p hp c hc) Q u z hz e v=
      (n+1 : ℕ)*e*r^p := by
  rw [valueCriticalContinuousMean_eq_source n (FiniteMixture.pure p hp c hc) hQ u hu z hz,hr]
  calc
    _=(n+1 : ℕ)*((FiniteMixture.pure p hp c hc).xi (Q*r)/
        (FiniteMixture.pure p hp c hc).xi Q)*e := by ring
    _=_ := by rw [pure_center_value_ratio p hp c hc hQ];ring

/-- Full continuous-field law under the actual proper-pure posterior,
with the exact physical residual model and all dimension factors. -/
theorem actual_pure_critical_latitude_continuous_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) (n d : ℕ) (hd : 0 < d)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (i : Vector d →ₗᵢ[ℝ] Vector (n+1)) (hi : ∀ x,inner ℝ (i x) u=0)
    (x : K → Vector d) (hx : Continuous x) (e : ℝ) :
    let μ := FiniteMixture.pure p hp c hc
    let θ := pureLatitudeResidual p hp c hc hQ hr
    let z := fun v => sourceUnitLatitudeMap u i r (x v)
    let hz : Continuous z := (sourceUnitLatitudeMap_continuous u i r).comp hx
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e).map
      (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        ContinuousMap.const K ((n+1 : ℕ)*e*r^p))=
      (stdGaussian (EuclideanDisorder d θ.maxDegree)).map
        (physicalResidualContinuousField θ (n+1) d x hx) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let θ := pureLatitudeResidual p hp c hc hQ hr
  let z := fun v => sourceUnitLatitudeMap u i r (x v)
  have hz : Continuous z := (sourceUnitLatitudeMap_continuous u i r).comp hx
  have hMean : valueCriticalContinuousMean n μ Q u z hz e=
      ContinuousMap.const K ((n+1 : ℕ)*e*r^p) := by
    ext v
    exact actual_pure_criticalContinuousMean p hp c hc hQ n u hu z hz e v
      (sourceUnitLatitudeMap_overlap (by omega) u hu i hi r (x v))
  rw [←hMean,actual_value_critical_centered_continuous_law n μ hQ u hu z hz e]
  apply continuous_field_law_eq_of_covariance
  intro v w
  rw [actual_value_critical_continuous_covariance n μ hQ u hu z hz v w
    (sourceUnitLatitudeMap_overlap (by omega) u hu i hi r (x v))
    (sourceUnitLatitudeMap_overlap (by omega) u hu i hi r (x w))
    (sourceUnitLatitudeMap_pair_overlap (by omega) u hu i hi hr (x v) (x w)),
    physicalResidualContinuousField_covariance θ (n+1) d hd x hx v w]
  change (n+1 : ℕ)*sourceValueTau (FiniteMixture.pure p hp c hc) Q r (inner ℝ (x v) (x w))=_
  rw [pure_valueTau_eq_residual_xi p hp c hc hQ hr]
  rfl

/-- The same proper-pure process transport written using the original
actual iid disorder law of the finite residual Hamiltonian. -/
theorem actual_pure_critical_latitude_tensor_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) (n d : ℕ) (hd : 0 < d)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (i : Vector d →ₗᵢ[ℝ] Vector (n+1)) (hi : ∀ x,inner ℝ (i x) u=0)
    (x : K → Vector d) (hx : Continuous x) (e : ℝ) :
    let μ := FiniteMixture.pure p hp c hc
    let θ := pureLatitudeResidual p hp c hc hQ hr
    let z := fun v => sourceUnitLatitudeMap u i r (x v)
    let hz : Continuous z := (sourceUnitLatitudeMap_continuous u i r).comp hx
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e).map
      (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        ContinuousMap.const K ((n+1 : ℕ)*e*r^p))=
      (disorderLaw d θ.maxDegree).map
        (fun J => physicalResidualContinuousField θ (n+1) d x hx (euclideanDisorder J)) := by
  dsimp only
  let θ := pureLatitudeResidual p hp c hc hQ hr
  have h := congrArg (fun ν => ν.map (physicalResidualContinuousField θ (n+1) d x hx))
    (actual_flattened_gaussian d θ.maxDegree).map_eq
  rw [Measure.map_map (physicalResidualContinuousField θ (n+1) d x hx).continuous.measurable
    (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)] at h
  exact (actual_pure_critical_latitude_continuous_law p hp c hc hQ hr n d hd u hu i hi x hx e).trans h.symm

end
end SlowEquilibration.SphericalCriticalLatitude
