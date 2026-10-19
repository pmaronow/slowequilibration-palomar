module
public import FourPapersCommon.MixedModel
public import Paper.JTVariational

@[expose] public section

/-! Exact measure transport under the actual covariance clock preserves
mixtures, is injective, and is continuous in the weak measure topology. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace FourPapersCommon

theorem probabilityMeasure_eq_of_cdf_on_unit (μ ν : Paper.ParisiMeasure)
    (he : ∀ q ∈ Icc (0 : ℝ) 1, Paper.parisiCDF μ q = Paper.parisiCDF ν q) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_Iic
  intro q
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact he q q.property

theorem mixedMeasure_injective (ξ : AdmissibleEvenMixture) :
    Function.Injective (mixedMeasure ξ) := by
  intro μ ν he
  apply probabilityMeasure_eq_of_cdf_on_unit
  intro q hq
  rw [← parisiCDF_mixedMeasure ξ μ q hq, ← parisiCDF_mixedMeasure ξ ν q hq, he]

theorem mixedMeasure_mix (ξ : AdmissibleEvenMixture) (μ ν : Paper.ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    mixedMeasure ξ (Paper.parisiMix μ ν t) =
      Paper.parisiMix (mixedMeasure ξ μ) (mixedMeasure ξ ν) t := by
  apply probabilityMeasure_eq_of_cdf_on_unit
  intro q hq
  obtain ⟨a,ha⟩ := ξ.surjective_unitClock ⟨q,hq⟩
  have he : ξ.clock (a : ℝ) = q := congrArg Subtype.val ha
  rw [← he,parisiCDF_mixedMeasure ξ (Paper.parisiMix μ ν t) a a.property,
    Paper.parisiCDF_mix μ ν t a ht,
    Paper.parisiCDF_mix (mixedMeasure ξ μ) (mixedMeasure ξ ν) t (ξ.clock a) ht,
    parisiCDF_mixedMeasure ξ μ a a.property,parisiCDF_mixedMeasure ξ ν a a.property]

theorem continuous_mixedMeasure (ξ : AdmissibleEvenMixture) :
    Continuous (mixedMeasure ξ) := ProbabilityMeasure.continuous_map ξ.continuous_unitClock

end FourPapersCommon
