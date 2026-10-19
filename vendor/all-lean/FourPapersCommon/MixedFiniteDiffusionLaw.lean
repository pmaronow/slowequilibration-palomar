module
public import FourPapersCommon.MixedFiniteBranching
public import FourPapersCommon.AllFieldStateApproximation
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-! The normalized finite branching kernels are the transition laws of the
actual selected mixed diffusion. This bridge retains endpoint atoms and
coincident finite-scheme overlap levels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open SpinGlass SpinGlass.Targets
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixedScalarTransition_eq_clockKernel (ξ : AdmissibleEvenMixture)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    mixedScalarTransition ξ μ a b m =
      FRSB.parisiConstantMassKernel (mixedBeta ξ) (mixedMeasure ξ μ)
        (ξ.clock a).toNNReal (ξ.clock b - ξ.clock a).toNNReal m := by
  have hca := ξ.clock_mem_unitInterval ha
  have hcb := ξ.clock_mem_unitInterval hb
  have hcab := ξ.clock_strictMonoOn.monotoneOn ha hb hab
  have hvar : mixedBeta ξ ^ 2 * (ξ.clock b - ξ.clock a) = ξ.first b - ξ.first a := by
    rw [mixedBeta_sq]
    unfold AdmissibleEvenMixture.clock
    field_simp [ξ.variance_pos.ne']
  unfold mixedScalarTransition FRSB.parisiConstantMassKernel
  rw [Real.coe_toNNReal _ hca.1, Real.coe_toNNReal _ (sub_nonneg.mpr hcab), hvar]
  congr 2
  funext y
  simp only [mixedPotential]
  congr 2
  ring

theorem measurable_mixedState (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Measurable (fun sample => mixedState ξ h μ sample q) :=
  measurable_selectedStateReal_time (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock_mem_unitInterval hq)

theorem mixedState_constantMass_restricted_transitionLaw (ξ : AdmissibleEvenMixture)
    (h : ℝ) (μ : ParisiMeasure) {a b m : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hc : ∀ q ∈ Ico a b, Paper.parisiCDF μ q = m)
    (E : Set BrownianSample)
    (hE : MeasurableSet[Paper.canonicalBrownianFiltration (ξ.clock a).toNNReal] E) :
    (Paper.canonicalBrownianMeasure.restrict E).map (fun sample => mixedState ξ h μ sample b) =
      mixedScalarTransition ξ μ a b m ∘ₘ
        (Paper.canonicalBrownianMeasure.restrict E).map (fun sample => mixedState ξ h μ sample a) := by
  have hca := ξ.clock_mem_unitInterval ha
  have hcb := ξ.clock_mem_unitInterval hb
  have hcl := ξ.clock_strictMonoOn ha hb hab
  have hnn : ((ξ.clock a).toNNReal : ℝ) = ξ.clock a := Real.coe_toNNReal _ hca.1
  have htnn : ((ξ.clock b - ξ.clock a).toNNReal : ℝ) = ξ.clock b - ξ.clock a :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hcl.le)
  have he : ((ξ.clock a).toNNReal : ℝ) + (ξ.clock b - ξ.clock a).toNNReal = ξ.clock b := by
    rw [hnn, htnn]
    ring
  have htpos : 0 < (ξ.clock b - ξ.clock a).toNNReal := by
    exact_mod_cast (show 0 < ((ξ.clock b - ξ.clock a).toNNReal : ℝ) by rw [htnn]; linarith)
  have H := FRSB.selectedParisiState_constantMass_restricted_transitionLaw
    (mixedBeta ξ) h (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ)
    (ξ.clock a).toNNReal (ξ.clock b - ξ.clock a).toNNReal htpos
    (by rw [he]; exact hcb.2) m (by
      simpa only [hnn, htnn, add_sub_cancel] using
        parisiCDF_mixedMeasure_constant_interval ξ μ ha hb hc) E hE
  have hstatea : Paper.selectedParisiItoState (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (ξ.clock a).toNNReal = fun sample => mixedState ξ h μ sample a := by
    funext sample
    rw [Paper.selectedParisiItoState_eq _ _ _ _ (by rw [hnn]; exact hca.2), hnn]
    rfl
  have hstateb : Paper.selectedParisiItoState (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) ((ξ.clock a).toNNReal + (ξ.clock b - ξ.clock a).toNNReal) =
        fun sample => mixedState ξ h μ sample b := by
    funext sample
    rw [Paper.selectedParisiItoState_eq _ _ _ _ (by simpa only [NNReal.coe_add] using he.le.trans hcb.2)]
    simp only [NNReal.coe_add, he]
    rfl
  rw [hstatea, hstateb, ← mixedScalarTransition_eq_clockKernel ξ μ ha hb hab.le] at H
  exact H

theorem mixedState_constantMass_transitionLaw (ξ : AdmissibleEvenMixture)
    (h : ℝ) (μ : ParisiMeasure) {a b m : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hc : ∀ q ∈ Ico a b, Paper.parisiCDF μ q = m) :
    Paper.canonicalBrownianMeasure.map (fun sample => mixedState ξ h μ sample b) =
      mixedScalarTransition ξ μ a b m ∘ₘ
        Paper.canonicalBrownianMeasure.map (fun sample => mixedState ξ h μ sample a) := by
  simpa only [Measure.restrict_univ] using
    mixedState_constantMass_restricted_transitionLaw ξ h μ ha hb hab hc Set.univ MeasurableSet.univ

theorem mixedState_schemeStep_transitionLaw {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 1) :
    Paper.canonicalBrownianMeasure.map
      (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q (p + 1))) =
      mixedSchemeScalarStep ξ s p ∘ₘ Paper.canonicalBrownianMeasure.map
        (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q p)) := by
  rcases lt_or_eq_of_le (s.q_mono p hp) with hlt | he
  · exact mixedState_constantMass_transitionLaw ξ h _
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩ hlt
      (fun _ hy => Paper.parisiCDF_scheme_cell s hp hy)
  · rw [mixedSchemeScalarStep_of_equal ξ s hp he, Measure.id_comp, he]

theorem mixedState_schemeEndpoint_law {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 2) :
    Paper.canonicalBrownianMeasure.map
      (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q p)) =
      mixedSchemeEndpointKernel ξ s 0 p h := by
  induction p with
  | zero =>
      simp only [s.q_zero, mixedState_initial, mixedSchemeEndpointKernel, Kernel.id_apply]
      simp
  | succ p ih =>
      rw [mixedState_schemeStep_transitionLaw ξ h s (by omega), ih (by omega),
        mixedSchemeEndpointKernel]
      simp only [Nat.zero_add]
      rfl

end FourPapersCommon
