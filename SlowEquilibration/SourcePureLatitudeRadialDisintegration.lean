-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeTransport
public import SlowEquilibration.SphericalLatitudeNormalization
public import SlowEquilibration.SphericalTAPLatitudeLIntegralChange

/-! The physical sphere as a radial mixture of its normalized latitude
laws. The radial measure carries the exact spherical coarea density. -/

@[expose] public section
namespace SlowEquilibration.SourcePureLatitudeRadialDisintegration
noncomputable section
open Set MeasureTheory SphericalModel
open SphericalTAPLatitudeLIntegralChange
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

def radialWeight (n : ℕ) (s : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  {t : Ioi (0 : ℝ) | (t : ℝ) < 2}.indicator
    (fun t => ENNReal.ofReal ((t : ℝ)*
      (Real.sqrt (1-(1-(t : ℝ)^2/2)^2))^(n-2))) s

def radialLaw (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  latitudeNormalization n •
    ((volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).withDensity
      (radialWeight n))

theorem radialWeight_measurable (n : ℕ) : Measurable (radialWeight n) := by
  unfold radialWeight
  apply Measurable.indicator
  · exact ENNReal.measurable_ofReal.comp (by fun_prop :
      Measurable (fun t : Ioi (0 : ℝ) => (t : ℝ)*
        (Real.sqrt (1-(1-(t : ℝ)^2/2)^2))^(n-2)))
  · exact measurableSet_Iio.preimage measurable_subtype_coe

theorem radial_latitude_expectation_measurable {n : ℕ}
    (u : Vector (n+1)) (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun s : Ioi (0 : ℝ) =>
      ∫⁻ v, F v ∂latitudeLaw u (latitudeFrameAt u)
        (1-(s : ℝ)^2/2)) := by
  let e := latitudeFrameAt u
  have hparam : Continuous (fun z : Ioi (0 : ℝ) × Vector n =>
      latitudeMap u e (1-(z.1 : ℝ)^2/2) z.2) := by
    unfold latitudeMap
    fun_prop
  have hjoint : Measurable (fun z : Ioi (0 : ℝ) × Vector n =>
      F (latitudeMap u e (1-(z.1 : ℝ)^2/2) z.2)) :=
    hF.comp hparam.measurable
  change Measurable (Function.uncurry
    (fun (s : Ioi (0 : ℝ)) (y : Vector n) =>
      F (latitudeMap u e (1-(s : ℝ)^2/2) y))) at hjoint
  have hm := hjoint.lintegral_prod_right (ν := sphereLaw n)
  convert hm using 1
  funext s
  unfold latitudeLaw
  rw [lintegral_map hF (latitudeMap_continuous u e (1-(s : ℝ)^2/2)).measurable]

/-- Exact physical one-spin coarea as a normalized radial mixture.
The identity holds for every nonnegative Borel observable. -/
theorem sphereLaw_lintegral_radialLaw {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂sphereLaw (n+1)) =
      ∫⁻ s : Ioi (0 : ℝ),
        (∫⁻ v, F v ∂latitudeLaw u (latitudeFrameAt u)
          (1-(s : ℝ)^2/2)) ∂radialLaw n := by
  have hw := radialWeight_measurable n
  have he := radial_latitude_expectation_measurable u F hF
  rw [radialLaw,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hw he]
  rw [sphereLaw_lintegral_latitudeLaw_at hn u hu F hF]
  simp only [latitudeNormalization,smul_eq_mul]
  congr 1
  apply lintegral_congr
  intro s
  by_cases hs : (s : ℝ) < 2
  · rw [Set.indicator_of_mem (show s ∈ {t : Ioi (0 : ℝ) | (t : ℝ)<2} from hs)]
    simp only [Pi.mul_apply,radialWeight,Set.indicator_of_mem
      (show s ∈ {t : Ioi (0 : ℝ) | (t : ℝ)<2} from hs)]
  · rw [Set.indicator_of_notMem (show s ∉ {t : Ioi (0 : ℝ) | (t : ℝ)<2} from hs)]
    simp only [Pi.mul_apply,radialWeight,Set.indicator_of_notMem
      (show s ∉ {t : Ioi (0 : ℝ) | (t : ℝ)<2} from hs),zero_mul]

/-- The source radial coarea measure is a genuine probability law. -/
theorem radialLaw_probability {n : ℕ} (hn : 2 ≤ n) :
    IsProbabilityMeasure (radialLaw n) := by
  refine ⟨?_⟩
  have h := sphereLaw_lintegral_radialLaw hn (latitudeChartPole n)
    (latitudeChartPole_norm_sq n) (fun _ => (1 : ℝ≥0∞)) measurable_const
  simpa using h.symm

end
end SlowEquilibration.SourcePureLatitudeRadialDisintegration
