-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureLatitudeRadialDisintegration

/-! The product of two physical sphere laws is the exact product mixture of
their latitude laws. Both radial parameters use the normalized coarea law. -/

@[expose] public section
namespace SlowEquilibration.SourcePureLatitudeProductRadialDisintegration
noncomputable section
open Set MeasureTheory SphericalModel
open SourcePureLatitudeRadialDisintegration
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem latitude_pair_expectation_measurable {n : ℕ}
    (u : Vector (n+1)) (F : (Vector (n+1) × Vector (n+1)) → ℝ≥0∞)
    (hF : Measurable F) :
    Measurable (fun s : Ioi (0 : ℝ) × Ioi (0 : ℝ) =>
      ∫⁻ z, F z ∂(latitudeLaw u (latitudeFrameAt u) (1-(s.1 : ℝ)^2/2)).prod
        (latitudeLaw u (latitudeFrameAt u) (1-(s.2 : ℝ)^2/2))) := by
  let e := latitudeFrameAt u
  have hparam : Continuous
      (fun z : (Ioi (0 : ℝ) × Ioi (0 : ℝ)) × (Vector n × Vector n) =>
        (latitudeMap u e (1-(z.1.1 : ℝ)^2/2) z.2.1,
         latitudeMap u e (1-(z.1.2 : ℝ)^2/2) z.2.2)) := by
    unfold latitudeMap
    fun_prop
  have hjoint : Measurable
      (fun z : (Ioi (0 : ℝ) × Ioi (0 : ℝ)) × (Vector n × Vector n) =>
        F (latitudeMap u e (1-(z.1.1 : ℝ)^2/2) z.2.1,
           latitudeMap u e (1-(z.1.2 : ℝ)^2/2) z.2.2)) :=
    hF.comp hparam.measurable
  have hm := hjoint.lintegral_prod_right'
    (ν := (sphereLaw n).prod (sphereLaw n))
  convert hm using 1
  funext s
  let f : Vector n → Vector (n+1) := latitudeMap u e (1-(s.1 : ℝ)^2/2)
  let g : Vector n → Vector (n+1) := latitudeMap u e (1-(s.2 : ℝ)^2/2)
  change (∫⁻ z, F z ∂(Measure.map f (sphereLaw n)).prod
      (Measure.map g (sphereLaw n))) =
    ∫⁻ z, F (Prod.map f g z) ∂(sphereLaw n).prod (sphereLaw n)
  rw [MeasureTheory.Measure.map_prod_map (sphereLaw n) (sphereLaw n)
    (latitudeMap_continuous u e _).measurable
    (latitudeMap_continuous u e _).measurable]
  exact lintegral_map hF ((latitudeMap_continuous u e _).measurable.prodMap
    (latitudeMap_continuous u e _).measurable)

/-- Exact two-spin coarea for every nonnegative Borel observable, including
overlap tests and mixed-radius bands. -/
theorem sphereLaw_prod_lintegral_radialLaw {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (F : (Vector (n+1) × Vector (n+1)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ z, F z ∂(sphereLaw (n+1)).prod (sphereLaw (n+1))) =
      ∫⁻ s : Ioi (0 : ℝ) × Ioi (0 : ℝ),
        (∫⁻ z, F z ∂(latitudeLaw u (latitudeFrameAt u)
          (1-(s.1 : ℝ)^2/2)).prod
          (latitudeLaw u (latitudeFrameAt u)
          (1-(s.2 : ℝ)^2/2)))
        ∂(radialLaw n).prod (radialLaw n) := by
  let μ := sphereLaw (n+1)
  let ρ := radialLaw n
  let L : Ioi (0 : ℝ) → Measure (Vector (n+1)) :=
    fun s => latitudeLaw u (latitudeFrameAt u) (1-(s : ℝ)^2/2)
  have : IsProbabilityMeasure ρ := radialLaw_probability hn
  have houter : Measurable (fun x : Vector (n+1) =>
      ∫⁻ y, F (x,y) ∂μ) := hF.lintegral_prod_right'
  have hradial : Measurable (fun s : Ioi (0 : ℝ) × Ioi (0 : ℝ) =>
      ∫⁻ z, F z ∂(L s.1).prod (L s.2)) :=
    latitude_pair_expectation_measurable u F hF
  calc
    (∫⁻ z, F z ∂μ.prod μ) = ∫⁻ x, ∫⁻ y, F (x,y) ∂μ ∂μ :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ s₁, ∫⁻ x, ∫⁻ y, F (x,y) ∂μ ∂L s₁ ∂ρ :=
      sphereLaw_lintegral_radialLaw hn u hu _ houter
    _ = ∫⁻ s₁, ∫⁻ y, ∫⁻ x, F (x,y) ∂L s₁ ∂μ ∂ρ := by
      apply lintegral_congr
      intro s₁
      exact lintegral_lintegral_swap (μ := L s₁) (ν := μ) hF.aemeasurable
    _ = ∫⁻ s₁, ∫⁻ s₂, ∫⁻ y, ∫⁻ x, F (x,y) ∂L s₁ ∂L s₂ ∂ρ ∂ρ := by
      apply lintegral_congr
      intro s₁
      have hinner : Measurable (fun y : Vector (n+1) =>
          ∫⁻ x, F (x,y) ∂L s₁) := hF.lintegral_prod_left'
      exact sphereLaw_lintegral_radialLaw hn u hu _ hinner
    _ = ∫⁻ s₁, ∫⁻ s₂, ∫⁻ z, F z ∂(L s₁).prod (L s₂) ∂ρ ∂ρ := by
      apply lintegral_congr
      intro s₁
      apply lintegral_congr
      intro s₂
      exact (lintegral_prod_symm' F hF).symm
    _ = ∫⁻ s : Ioi (0 : ℝ) × Ioi (0 : ℝ),
          (∫⁻ z, F z ∂(L s.1).prod (L s.2)) ∂ρ.prod ρ :=
      (lintegral_prod _ hradial.aemeasurable).symm

end
end SlowEquilibration.SourcePureLatitudeProductRadialDisintegration
