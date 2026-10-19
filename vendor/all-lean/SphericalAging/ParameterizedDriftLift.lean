module

public import SphericalAging.ParameterizedItoLift
public import SphericalAging.PredictableTerminalOperators

public section

/-! Actual deterministic Fubini for independent parameter families of
predictable L² coefficients. The equality is proved from genuine product
almost-everywhere sections of the actual coefficient representatives; it
holds simultaneously at every terminal time.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ParameterizedDriftLift
open HardSphereDynamics IndependentBackgroundDriver PredictableDriftTime ParameterizedItoLift
variable {A Ω : Type*} [mA : MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}
set_option maxHeartbeats 1800000

/-- Actual drift versions commute with the independent parameter-family
lift, on one common event for every deterministic terminal time. -/
theorem driftVersion_familyLift (T : ℝ≥0)
    (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    ∀ᵐ a ∂ρ, ∀ᵐ ω ∂P, ∀ t,
      driftVersion (PredictableFamilyLift.familyLift f) T t (a,ω) =
        driftVersion (f a) T t ω := by
  let V := PredictableFamilyLift.familyLift f
  have hv := (unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (representative_ae V)
  filter_upwards [Measure.ae_ae_of_ae_prod hv,predictableFamily_slice_ae f] with a hv hf
  have hrep : (fun z : ℝ≥0 × Ω => representative V (z.1,(a,z.2)))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] representative (f a) := by
    filter_upwards [hv,hf,representative_ae (f a)] with z hv hf hfa
    exact hv.trans (hf.trans hfa.symm)
  have hcut : (fun z : ℝ≥0 × Ω => cutRepresentative V T (z.1,(a,z.2)))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] cutRepresentative (f a) T := by
    filter_upwards [hrep] with z hz
    simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator,Set.mem_prod,Set.mem_univ,and_true,hz]
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hcut
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  intro t
  unfold driftVersion primitive
  apply integral_congr_ae
  exact ae_restrict_of_ae hω

end SphericalAging.ParameterizedDriftLift
