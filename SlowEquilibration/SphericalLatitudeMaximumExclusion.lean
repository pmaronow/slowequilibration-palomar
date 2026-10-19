-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeMaximum
public import Mathlib.Probability.Moments.Basic

@[expose] public section

/-! Genuine finite-volume maximum exclusion from the actual marked critical
count and an internally proved Gaussian fixed-point lower-tail estimate. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actual_field_lower_tail {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hv : 0 < covariancePolynomial c 1)
    (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) {δ : ℝ} (hδ : 0 ≤ δ) :
    disorderLaw N P {J | field c J x < -(N : ℝ)*δ} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ)*δ^2/(2*covariancePolynomial c 1))) := by
  let t := -δ/covariancePolynomial c 1
  have ht : t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) hv.le
  have h := measure_le_le_exp_mul_mgf (μ := disorderLaw N P) (X := fun J => field c J x)
    (-(N : ℝ)*δ) ht (field_exp_integrable c x t)
  rw [mgf, field_exp_integral_on_sphere hN c hc x hx t, ← Real.exp_add] at h
  have he : -t*(-(N : ℝ)*δ)+(N : ℝ)*t^2*covariancePolynomial c 1/2 =
      -(N : ℝ)*δ^2/(2*covariancePolynomial c 1) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at h
  have hle : disorderLaw N P {J | field c J x ≤ -(N : ℝ)*δ} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ)*δ^2/(2*covariancePolynomial c 1))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (disorderLaw N P) _)]
    exact ENNReal.ofReal_le_ofReal h
  apply le_trans (measure_mono ?_) hle
  intro J hJ
  change field c J x < -(N : ℝ)*δ at hJ
  change field c J x ≤ -(N : ℝ)*δ
  exact hJ.le

theorem latitudeField_jointContinuous {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    Continuous (fun p : Disorder (n+2) P × Vector (n+1) => latitudeField c p.1 w e q p.2) := by
  have hp : Continuous (fun p : Disorder (n+2) P × Vector (n+1) => (p.1, latitudeMap w e q p.2)) := by
    unfold latitudeMap
    fun_prop
  exact (field_jointContinuous c).comp hp

/-- A genuine low-maximum event is bounded by a Gaussian fixed-point tail
plus the expected actual number of critical points in the remaining height
window. All geometric criticality and measurability facts are internal. -/
theorem latitude_low_maximum_probability_le {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (hfirst : 0 < firstCovariance c 1) (hv : 0 < covariancePolynomial c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ) (U : ℝ) :
    disorderLaw (n+2) P {J | ∀ y, ‖y‖^2=((n+1 : ℕ) : ℝ) → latitudeField c J w e q y ≤ U} ≤
      ENNReal.ofReal (Real.exp (-((n+2 : ℕ) : ℝ)*δ^2/(2*covariancePolynomial c 1))) +
        ∫⁻ J, actualLatitudeSphereCount c w e q
          (fun J y => if latitudeField c J w e q y ∈ Icc (-((n+2 : ℕ) : ℝ)*δ) U then 1 else 0) J
            ∂disorderLaw (n+2) P := by
  classical
  let L := -((n+2 : ℕ) : ℝ)*δ
  let C := actualLatitudeSphereCount c w e q
    (fun J y => if latitudeField c J w e q y ∈ Icc L U then 1 else 0)
  have hmark : Measurable (fun p : Disorder (n+2) P × Vector (n+1) =>
      if latitudeField c p.1 w e q p.2 ∈ Icc L U then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_Icc.preimage (latitudeField_jointContinuous c w e q).measurable)
      measurable_const measurable_const
  have hC : AEMeasurable C (disorderLaw (n+2) P) :=
    (actual_latitude_sphere_marked_kacRice hn c hc hfirst w hw e he hq _ hmark).1
  have hsub : {J | ∀ y, ‖y‖^2=((n+1 : ℕ) : ℝ) → latitudeField c J w e q y ≤ U} ⊆
      {J | latitudeField c J w e q x < L} ∪ {J | 1 ≤ C J} := by
    intro J hJ
    by_cases hL : L ≤ latitudeField c J w e q x
    · exact Or.inr (latitude_count_ge_one_of_low_maximum c w e q J x hx hL hJ)
    · exact Or.inl (lt_of_not_ge hL)
  have ht := actual_field_lower_tail (by omega) c hc hv (latitudeMap w e q x)
    (latitudeMap_norm_sq (by omega) w hw e he hq.le x hx) hδ
  have hm : disorderLaw (n+2) P {J | 1 ≤ C J} ≤ ∫⁻ J, C J ∂disorderLaw (n+2) P := by
    simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ht hm))

end
end SlowEquilibration.SphericalLatitudeChartKacRice
