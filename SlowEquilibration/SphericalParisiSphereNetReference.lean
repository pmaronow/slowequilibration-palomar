-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiSphereNetPressure
public import SlowEquilibration.SphericalParisiLabeledOriginalEndpoint

/-! Actual finite probability references for the sphere, with an exact
identification of their Gaussian spin pressure and the finite-net pressure. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel PureTensorJetBounds FiniteTensorMixtureMaximum
open SphericalParisiGroundRSUpper SphericalParisiLabeledOriginalEndpoint
open SphericalParisiGaussianREMJensen
open GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {N k : ℕ}

def netReference [NeZero k] (points : Fin k → UnitSphere N) : Measure (UnitSphere N) :=
  Measure.map points (labelLaw k)

instance netReference_probability [NeZero k] (points : Fin k → UnitSphere N) :
    IsProbabilityMeasure (netReference points) := by
  unfold netReference
  infer_instance

omit [DecidableEq σ] in
theorem netReference_logPartition [NeZero k] (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) (β : ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    logPartition (netReference points) (spinLinear d c β) g = netLogAverage d c points β g := by
  unfold logPartition GaussianSpinInterpolation.moment weight netReference netLogAverage logAverageExp
  simp only [one_mul]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite points)
    (((spinLinear_continuous d c β).clm_apply continuous_const).rexp.stronglyMeasurable),
    labelLaw_integral]
  simp only [spinLinear,innerSL_apply_apply,real_inner_smul_left]

omit [DecidableEq σ] in
theorem netReference_pressure [NeZero k] (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) (β : ℝ) :
    originalSpinPressure (netReference points) d c β =
      ∫ g,netLogAverage d c points β g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d) := by
  unfold originalSpinPressure
  exact integral_congr_ae (.of_forall (netReference_logPartition d c points β))

theorem exists_actual_netReference_ground_pressure_bound (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hd : ∀ i,1 ≤ d i)
    {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ μ : Measure (UnitSphere N),IsProbabilityMeasure μ ∧
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        originalSpinPressure μ d c β/(β*(N : ℝ))+
          Real.log (1+2/ε)/β+derivativeConstant d c*ε := by
  obtain ⟨k,points,hk,_hcover,_hcard,H⟩ := exists_actual_net_ground_pressure_bound hN d c hd hε hβ
  let : NeZero k := ⟨hk.ne'⟩
  refine ⟨netReference points,inferInstance,?_⟩
  rw [← netReference_pressure d c points β] at H
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have HD := div_le_div_of_nonneg_right H hNr.le
  apply HD.trans_eq
  field_simp [hNr.ne',hβ.ne']

/-- A genuine internally constructed sphere-reference family. The finite
cover, its entropy and the Gaussian derivative approximation are all proved
inside the construction, rather than supplied as hypotheses. -/
theorem exists_actual_netReference_family (d : σ → ℕ) (c : σ → ℝ)
    (hd : ∀ i,1 ≤ d i) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ μ : (N : ℕ) → Measure (UnitSphere N),
      (∀ N,0 < N → IsProbabilityMeasure (μ N)) ∧
      (∀ N,0 < N →
        (∫ g,actualMaximum (N := N) d c g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
          originalSpinPressure (μ N) d c β/(β*(N : ℝ))+
            Real.log (1+2/ε)/β+derivativeConstant d c*ε) := by
  classical
  have H : ∀ N : ℕ,∃ μ : Measure (UnitSphere N),0 < N →
      IsProbabilityMeasure μ ∧
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        originalSpinPressure μ d c β/(β*(N : ℝ))+
          Real.log (1+2/ε)/β+derivativeConstant d c*ε := by
    intro N
    by_cases hN : 0 < N
    · obtain ⟨μ,hμ,hb⟩ := exists_actual_netReference_ground_pressure_bound hN d c hd hε hβ
      exact ⟨μ,fun _ => ⟨hμ,hb⟩⟩
    · exact ⟨0,fun hn => (hN hn).elim⟩
  choose μ hμ using H
  exact ⟨μ,(fun N hN => (hμ N hN).1),(fun N hN => (hμ N hN).2)⟩

end SlowEquilibration.SphericalParisiSphereNet
