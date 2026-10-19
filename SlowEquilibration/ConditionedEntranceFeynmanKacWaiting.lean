-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacRestart

/-! Actual cumulative-hazard weights are observed in the full waiting
filtration. The adapted representative is constructed from the proved
predictable time-cut, including its null paths. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics PredictableDriftTime FourPapersCommon
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E Ω : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

omit [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [SecondCountableTopology E] in
/-- There is a genuinely waiting-measurable representative in [0,1] of
the literal survival probability, without a measurability premise on the
occupation itself. -/
theorem survival_waiting_representative (κ : E → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ x, 0 ≤ κ x) (X : ℝ≥0 → Ω → E) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) (s : ℝ≥0) :
    ∃ H : Ω → ℝ, StronglyMeasurable[F s] H ∧
      (∀ ω, 0 ≤ H ω ∧ H ω ≤ 1) ∧ H =ᵐ[P] survival κ X s := by
  let G : ℝ≥0 → Ω → ℝ := fun t ω => κ (X t ω)
  have hGa : StronglyAdapted F G := fun t => hκ.comp_stronglyMeasurable (hXa t)
  have hGc : ∀ᵐ ω ∂P, Continuous (fun t => G t ω) :=
    hXc.mono (fun _ hc => hκ.comp hc)
  let W := continuousAdaptedTimeCut G s
  have hW : AEStronglyMeasurable[F.predictable] W (nonnegativeLebesgueMeasure.prod P) :=
    aestronglyMeasurable_aeContinuousAdaptedTimeCut F G hGa hGc s
  let V := hW.mk W
  have hV : StronglyMeasurable[F.predictable] V := hW.stronglyMeasurable_mk
  have hprim := primitive_stronglyAdapted V hV
  let H : Ω → ℝ := fun ω => min 1 (max 0 (Real.exp (-primitive V s ω)))
  have hclip : Continuous (fun r : ℝ => min 1 (max 0 (Real.exp (-r)))) := by fun_prop
  have hHm : StronglyMeasurable[F s] H := hclip.comp_stronglyMeasurable (hprim s)
  refine ⟨H,hHm,fun ω => ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩,?_⟩
  have hswap : (fun q : Ω × ℝ≥0 => W (q.2,q.1)) =ᵐ[P.prod nonnegativeLebesgueMeasure]
      fun q => V (q.2,q.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hW.ae_eq_mk
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  have he : primitive V s ω = occupation κ X s ω := by
    calc
      primitive V s ω = ∫ r in Ioc (0 : ℝ≥0) s, W (r,ω) ∂nonnegativeLebesgueMeasure := by
        apply integral_congr_ae
        exact ae_restrict_of_ae (hω.mono (fun _ h => h.symm))
      _ = ∫ r in Ioc (0 : ℝ≥0) s, G r ω ∂nonnegativeLebesgueMeasure := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        simp only [W,continuousAdaptedTimeCut,ite_eq_left hr]
      _ = occupation κ X s ω :=
        primitive_eq_real_intervalIntegral (fun q : ℝ≥0 × Ω => G q.1 q.2) s ω
  dsimp only [H]
  rw [he]
  change min 1 (max 0 (survival κ X s ω)) = survival κ X s ω
  rw [max_eq_right (survival_nonneg κ X s ω),min_eq_right (survival_le_one κ hκ0 X s ω)]

end SlowEquilibration.ConditionedEntrance.FeynmanKac
