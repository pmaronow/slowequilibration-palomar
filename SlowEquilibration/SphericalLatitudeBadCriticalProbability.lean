-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeGlobalCount

@[expose] public section

/-! Literal existence of a bad affine-sphere critical point is bounded by
its genuine marked Kac--Rice count, including measurability of that count. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalForm
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_bad_critical_probability_le_count {n P : ℕ} (hn : 1≤n)
    (c : Degree P → ℝ) (hc : ∀ p,0≤c p) (hfirst : 0<firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q|<1) (E : Set (Disorder (n+2) P × Vector (n+1))) (hE : MeasurableSet E) :
    disorderLaw (n+2) P {J | ∃ y,‖y‖^2=((n+1 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0 ∧ (J,y)∈E}≤
      ∫⁻ J,actualLatitudeSphereCount c w e q (fun J y => if (J,y)∈E then 1 else 0) J
        ∂disorderLaw (n+2) P := by
  let psi : Disorder (n+2) P → Vector (n+1) → ℝ≥0∞ := fun J y => if (J,y)∈E then 1 else 0
  let C := actualLatitudeSphereCount c w e q psi
  have hpsi : Measurable (fun p : Disorder (n+2) P × Vector (n+1) => psi p.1 p.2) :=
    Measurable.ite hE measurable_const measurable_const
  have hC : AEMeasurable C (disorderLaw (n+2) P) :=
    (actual_latitude_sphere_marked_kacRice hn c hc hfirst w hw e he hq psi hpsi).1
  have hsub : {J | ∃ y,‖y‖^2=((n+1 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0 ∧ (J,y)∈E}⊆{J | 1≤C J} := by
    rintro J ⟨y,hy,hcrit,hbad⟩
    have ht := ENNReal.le_tsum (f := fun z : {z : Vector (n+1) | ‖z‖^2=((n+1 : ℕ) : ℝ) ∧
        surfaceGradient (latitudeField c J w e q) z=0} => psi J z) ⟨y,hy,hcrit⟩
    simpa only [psi,ite_eq_left hbad,actualLatitudeSphereCount,C,Set.mem_setOf_eq] using ht
  apply (measure_mono hsub).trans
  simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1

end
end SlowEquilibration.SphericalLatitudeChartKacRice
