module

public import SphericalAging.StrongUniqueness
public import Mathlib.MeasureTheory.Measure.OpenPos

public section

/-! Equality of actual continuous state paths follows from equality of
their positive-horizon product-measure time cuts. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ContinuousTimeCut
open HardSphereDynamics
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

instance nonnegativeLebesgueMeasure_isOpenPosMeasure : Measure.IsOpenPosMeasure nonnegativeLebesgueMeasure where
  open_pos U hU hne := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨b,hxb,hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
      (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx))
    apply ne_of_gt
    calc
      0 < nonnegativeLebesgueMeasure (Ioc x b) := by
        rw [nonnegativeLebesgueMeasure_Ioc]
        exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (by exact_mod_cast hxb))
      _ ≤ nonnegativeLebesgueMeasure U := measure_mono hsub

 theorem common_path_of_timeCut {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0} (hT : 0 < T)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
    (heq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = Y t omega := by
  have hp := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heq)
  filter_upwards [hp,hXc,hYc] with omega hp hx hy
  have hIoc : (fun t => X t omega) =ᵐ[nonnegativeLebesgueMeasure.restrict (Ioc 0 T)]
      (fun t => Y t omega) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hp] with t ht hmem
    simpa only [Prod.swap_prod_mk,indicator_of_mem (show (t,omega) ∈ Ioc 0 T ×ˢ (univ : Set Ω)
      from ⟨hmem,mem_univ _⟩)] using ht
  have hIcc : (fun t => X t omega) =ᵐ[nonnegativeLebesgueMeasure.restrict (Icc 0 T)]
      (fun t => Y t omega) := by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := nonnegativeLebesgueMeasure))]
    exact hIoc
  exact fun t ht => Measure.eqOn_Icc_of_ae_eq nonnegativeLebesgueMeasure (ne_of_lt hT)
    hIcc hx.continuousOn hy.continuousOn ⟨zero_le,ht⟩
end SphericalAging.ContinuousTimeCut
