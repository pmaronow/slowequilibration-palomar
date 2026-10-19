module

public import SphericalAging.AffineSDEFourthMoment

public section

/-! Sharp first-moment Grönwall for the actual radial integral equation.
The exponent grows linearly in the drift bound; this is needed when
integrating variational estimates under the Gaussian disorder law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SharpRadialMoment
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto LinearSDEFourthMoment
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def firstMoment (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ := ∫ ω,Z t ω ∂P

theorem firstMoment_continuous (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P,Continuous (fun t => Z t ω)) (L : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P,∀ t,‖Z t ω‖ ≤ L) : Continuous (firstMoment (P := P) Z) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (L : ℝ))
  · intro n
    exact ((hZa (u n)).mono (F.le _)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact hbound.mono (fun _ hh => hh (u n))
  · filter_upwards [hZc] with ω hω
    exact (hω.tendsto t).comp hu

theorem timeCut_integrable (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P,Continuous (fun t => Z t ω)) (L : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P,∀ t,‖Z t ω‖ ≤ L) (t : ℝ≥0) :
    Integrable (FourPapersCommon.continuousAdaptedTimeCut Z t) (nonnegativeLebesgueMeasure.prod P) := by
  apply memLp_one_iff_integrable.mp
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 1
    (measurableSet_Ioc.prod MeasurableSet.univ) (L : ℝ)
    (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle t))
  apply hg.mono' ((FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut
    F Z hZa hZc t).mono (predictable_le_prod F))
  have hae := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hbound
  filter_upwards [hae] with q hq
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) t
  · simpa [FourPapersCommon.continuousAdaptedTimeCut,ht,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Real.norm_of_nonneg L.coe_nonneg] using hq q.1
  · simp [FourPapersCommon.continuousAdaptedTimeCut,ht,FourPapersCommon.FilteredBrownian.predictableTimeFrame]

theorem expectation_driftVersion (A : PredictableProcessL2 F P) (t : ℝ≥0) :
    (∫ ω,driftVersion A t t ω ∂P) =
      ∫ q,cutRepresentative A t q ∂nonnegativeLebesgueMeasure.prod P := by
  rw [integral_prod_symm _ (cutRepresentative_integrable A t)]
  apply integral_congr_ae
  exact .of_forall (fun ω => by
    unfold driftVersion primitive
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) t
      · simp [hs]
      · simp [hs,cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame]))

theorem vectorProcessLp_expectation_zero (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) (t : ℝ≥0) :
    (∫ ω,(vectorProcessLp D U t : Ω → ℝ) ω ∂P)=0 := by
  unfold vectorProcessLp vectorIto
  rw [← generalExpectationMap_apply,map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [generalExpectationMap_apply]
  exact integral_naturalItoIntegral (D.filtered j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j) _

/-- The actual scalar equation has a first-moment estimate with exponent
M, using zero expectation of the constructed Itô term. -/
theorem scalar_equation_firstMoment (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P,Continuous (fun t => Z t ω)) (L M : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P,∀ t,‖Z t ω‖ ≤ L) (T : ℝ≥0) (z0 : ℝ)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (A : TimeProcessL2 P) q ≤ (M : ℝ)*Z q.1 q.2)
    (heq : ∀ t,t ≤ T → ∀ᵐ ω ∂P,Z t ω=z0+driftVersion A t t ω+
      (vectorProcessLp D U t : Ω → ℝ) ω) (t : ℝ≥0) (ht : t ≤ T) :
    firstMoment (P := P) Z t ≤ z0*Real.exp ((M : ℝ)*t) := by
  have hc := firstMoment_continuous Z hZa hZc L hbound
  have hb (s : ℝ≥0) (hs : s ≤ T) : firstMoment (P := P) Z s ≤
      z0+(M : ℝ)*∫ r in Ioc (0 : ℝ≥0) s,firstMoment (P := P) Z r ∂nonnegativeLebesgueMeasure := by
    have hZi := (bounded_memLp Z hZa L hbound s).integrable (by norm_num)
    have hAi := (driftVersion_memLp A s s).integrable (by norm_num)
    have hUi := (Lp.memLp (vectorProcessLp D U s)).integrable (by norm_num)
    have he : firstMoment (P := P) Z s=z0+∫ ω,driftVersion A s s ω ∂P := by
      unfold firstMoment
      rw [integral_congr_ae (heq s hs)]
      have h1 := integral_add ((integrable_const z0).add hAi) hUi
      have h2 := integral_add (integrable_const z0) hAi
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2,integral_const,vectorProcessLp_expectation_zero]
      simp
    rw [he,expectation_driftVersion]
    refine add_le_add le_rfl ?_
    have hcut := timeCut_integrable Z hZa hZc L hbound s
    calc
      _ ≤ ∫ q,(M : ℝ)*FourPapersCommon.continuousAdaptedTimeCut Z s q
          ∂nonnegativeLebesgueMeasure.prod P := by
        apply integral_mono_ae (cutRepresentative_integrable A s) (hcut.const_mul _)
        filter_upwards [representative_ae A,hA] with q hr ha
        by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) s
        · simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
            indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω) from ⟨hq,mem_univ _⟩),
            FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,hr]
          exact ha ⟨hq.1,hq.2.trans hs⟩
        · simp [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,FourPapersCommon.continuousAdaptedTimeCut,hq]
      _ = _ := by
        rw [integral_const_mul,integral_prod _ hcut,← integral_indicator measurableSet_Ioc]
        congr 1
        apply integral_congr_ae
        exact .of_forall (fun r => by
          by_cases hr : r ∈ Ioc (0 : ℝ≥0) s
          · simp [FourPapersCommon.continuousAdaptedTimeCut,hr,firstMoment]
          · simp [FourPapersCommon.continuousAdaptedTimeCut,hr])
  have hf : Continuous (fun r : ℝ => firstMoment (P := P) Z r.toNNReal) :=
    hc.comp continuous_real_toNNReal
  have hgr := integral_gronwall_bound (fun r => firstMoment (P := P) Z r.toNNReal)
    z0 M T M.coe_nonneg hf (by
      intro r hr
      have hrs : r.toNNReal ≤ T := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2
      have hh := hb r.toNNReal hrs
      have he : (∫ s in Ioc (0 : ℝ≥0) r.toNNReal,firstMoment (P := P) Z s ∂nonnegativeLebesgueMeasure)=
          ∫ s in (0 : ℝ)..(r.toNNReal : ℝ),firstMoment (P := P) Z s.toNNReal :=
        primitive_eq_real_intervalIntegral (fun q : ℝ≥0 × Unit => firstMoment (P := P) Z q.1) _ ()
      rw [he,Real.coe_toNNReal _ hr.1] at hh
      exact hh)
  simpa only [Real.toNNReal_coe] using hgr t ⟨t.coe_nonneg,ht⟩

end SphericalAging.SharpRadialMoment
