module
public import Paper.ParisiGradientMartingale

@[expose] public section

/-! Centered Itô increments with a genuine bounded measurable source term. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped NNReal Topology
namespace FRSB

/-- All Fubini and integrability obligations for a bounded measurable source. -/
theorem bounded_source_fubini {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (B : ℝ) (hb : ∀ s ω, ‖g s ω‖ ≤ B)
    (a b : ℝ) (hab : a ≤ b) :
    Integrable (fun ω => ∫ s in a..b, g s ω) P ∧
      (∫ ω, (∫ s in a..b, g s ω) ∂P) = ∫ s in a..b, ∫ ω, g s ω ∂P := by
  let τ : Measure ℝ := volume.restrict (Ioc a b)
  have : IsFiniteMeasure τ := by dsimp [τ]; infer_instance
  let f : Ω → ℝ → ℝ := fun ω s => g s ω
  have hm : Measurable (Function.uncurry f) := hg.comp measurable_swap
  have hi : Integrable (Function.uncurry f) (P.prod τ) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (.of_forall fun p => hb p.2 p.1)
  have he : (fun ω => ∫ s in a..b, g s ω) = fun ω => ∫ s, f ω s ∂τ := by
    funext ω
    rw [intervalIntegral.integral_of_le hab]
  refine ⟨he ▸ hi.integral_prod_left, ?_⟩
  rw [he, intervalIntegral.integral_of_le hab]
  exact integral_integral_swap hi

/-- The actual centered stochastic remainder bounds the expectation increment
minus the expected time source. No stochastic centering assumption is supplied. -/
theorem ito_expectation_source_error {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ≥0) (hab : a ≤ b) (K : ℝ≥0)
    (hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (source : ℝ → Ω → ℝ) (hm : Measurable (Function.uncurry source))
    (B : ℝ) (hb : ∀ s ω, ‖source s ω‖ ≤ B)
    (E : ℝ → ℝ) (hE : IntervalIntegrable E volume a b)
    (hgen : ∀ ω, ∀ s ∈ Icc (a : ℝ) (b : ℝ),
      ‖Paper.hjbGenerator X d β f s ω - source s ω‖ ≤ E s)
    (hia : Integrable (fun ω => f a (X a ω)) P)
    (hib : Integrable (fun ω => f b (X b ω)) P) :
    ‖(∫ ω, f b (X b ω) ∂P) - (∫ ω, f a (X a ω) ∂P) -
      ∫ s in (a : ℝ)..(b : ℝ), ∫ ω, source s ω ∂P‖ ≤ ∫ s in (a : ℝ)..(b : ℝ), E s := by
  obtain ⟨N,hN,_hZN,hzero,hformula⟩ := Paper.ito_weighted_increment hc f hf htdiff hslice
    hdt hdx hsecond a b hab K hK (fun _ => 1) stronglyMeasurable_const 1 (by simp)
  simp only [one_mul] at hzero
  let R : Ω → ℝ := fun ω => ∫ s in (a : ℝ)..(b : ℝ), source s ω
  obtain ⟨hiR,hR⟩ := bounded_source_fubini P source hm B hb a b (NNReal.coe_le_coe.mpr hab)
  let G : Ω → ℝ := fun ω => ∫ s in (a : ℝ)..(b : ℝ),
    (Paper.hjbGenerator X d β f s ω - source s ω)
  have his (ω : Ω) : IntervalIntegrable (fun s => source s ω) volume a b := by
    apply (intervalIntegrable_const (c := B)).mono_fun'
      ((hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    exact .of_forall (hb · ω)
  have hiGen (ω : Ω) : IntervalIntegrable (fun s => Paper.hjbGenerator X d β f s ω) volume a b :=
    IntegrableOn.intervalIntegrable (by
      simpa only [uIcc_of_le (NNReal.coe_le_coe.mpr hab)] using
        Paper.hjbGenerator_integrableOn hc f hdt hdx hsecond a b ω)
  have heq : G =ᵐ[P] fun ω => f b (X b ω) - f a (X a ω) - N ω - R ω := by
    filter_upwards [hformula] with ω hω
    dsimp only [G,R]
    rw [intervalIntegral.integral_sub (hiGen ω) (his ω)]
    linarith
  have hiG : Integrable G P := (((hib.sub hia).sub hN).sub hiR).congr heq.symm
  have hn : ∀ᵐ ω ∂P, ‖G ω‖ ≤ ∫ s in (a : ℝ)..(b : ℝ), E s :=
    .of_forall fun ω => intervalIntegral.norm_integral_le_of_norm_le
      (NNReal.coe_le_coe.mpr hab)
      (.of_forall fun s hs => hgen ω s ⟨hs.1.le,hs.2⟩) hE
  have heg : (∫ ω, G ω ∂P) =
      (∫ ω, f b (X b ω) ∂P) - (∫ ω, f a (X a ω) ∂P) -
        ∫ s in (a : ℝ)..(b : ℝ), ∫ ω, source s ω ∂P := by
    rw [integral_congr_ae heq]
    have hs1 := integral_sub (f := fun ω => f b (X b ω) - f a (X a ω) - N ω)
      (g := R) ((hib.sub hia).sub hN) hiR
    have hs2 := integral_sub (f := fun ω => f b (X b ω) - f a (X a ω))
      (g := N) (hib.sub hia) hN
    have hs3 := integral_sub (f := fun ω => f b (X b ω))
      (g := fun ω => f a (X a ω)) hib hia
    rw [hs1,hs2,hs3,hzero,sub_zero]
    exact congrArg (fun z => (∫ ω, f b (X b ω) ∂P) -
      (∫ ω, f a (X a ω) ∂P) - z) hR
  rw [← heg]
  simpa using norm_integral_le_of_norm_le_const hn

end FRSB
