module
public import FourPapersCommon.SignedColeHopfDatum
public import FourPapersCommon.ScalarBrownianControl

@[expose] public section

/-! Signed scalar Brownian verification on a compact subinterval before the
terminal variance vanishes. The expectation identity follows from the actual
Itô characteristics and actual logarithmic Gaussian heat derivatives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus FRSB
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

theorem integrable_bounded_intervalIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℝ → Ω → ℝ)
    (hf : Measurable (Function.uncurry f)) (C : ℝ) (hC : ∀ s sample,‖f s sample‖≤C)
    (a b : ℝ) (hab : a≤b) : Integrable (fun sample=>∫ s in a..b,f s sample) P := by
  have hi := hf.stronglyMeasurable.integral_prod_left' (μ:=volume.restrict (Ioc a b))
  have hm : Measurable (fun sample=>∫ s in a..b,f s sample) := by
    simpa only [intervalIntegral.integral_of_le hab,Function.uncurry] using hi.measurable
  apply (integrable_const (C*|b-a|)).mono' hm.aestronglyMeasurable
  exact .of_forall (fun sample=>intervalIntegral.norm_integral_le_of_norm_le_const (fun s _=>hC s sample))

theorem integrable_lipschitz_scalarControlledState (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A)
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    Integrable (fun sample=>f (scalarControlledState m x A t sample)) canonicalBrownianMeasure := by
  have hi := (integrable_scalarControlledState m x A hA t).norm.const_mul (L : ℝ)
  apply ((integrable_const ‖f 0‖).add hi).mono'
    (hL.continuous.measurable.comp
      (((stronglyAdapted_scalarControlledState m x A hA t).mono
        (canonicalBrownianFiltration.le t)).measurable)).aestronglyMeasurable
  apply Eventually.of_forall
  intro sample
  calc
    ‖f (scalarControlledState m x A t sample)‖ ≤
      ‖f 0‖+‖f (scalarControlledState m x A t sample)-f 0‖ := by
        have hn := norm_add_le (f 0) (f (scalarControlledState m x A t sample)-f 0)
        have he : f 0+(f (scalarControlledState m x A t sample)-f 0)=
            f (scalarControlledState m x A t sample) := by ring
        rw [he] at hn
        exact hn
    _ ≤ _ := by
      dsimp only [Pi.add_apply]
      gcongr
      simpa only [dist_eq_norm,sub_zero] using hL.dist_le_mul
        (scalarControlledState m x A t sample) 0

def signedControlGapSource (F : ℝ → ℝ) (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) (s : ℝ) (sample : BrownianSample) : ℝ :=
  m/2*(A s sample^2-(A s sample-signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
    (scalarControlledState m x A s.toNNReal sample))^2)

theorem measurable_signedControlGapSource {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) :
    Measurable (Function.uncurry (signedControlGapSource F m x A)) := by
  have hDx := (continuous_signedHeatLog_jets (hF.expHeatDatum m) m
    (fun v y=>(gaussianHeatFlow_exp_pos hF m v y).ne')).2.1
  have hX : Measurable (fun p : ℝ × BrownianSample=>scalarControlledState m x A p.1.toNNReal p.2) :=
    (measurable_scalarControlledState m x A hA).comp
      (measurable_real_toNNReal.prodMap measurable_id)
  exact ((hA.measurable.pow_const 2).sub
    ((hA.measurable.sub (hDx.measurable.comp
      ((measurable_const.sub measurable_fst).prodMk hX))).pow_const 2)).const_mul (m/2)

theorem norm_signedControlGapSource_le {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m≠0) (A : ℝ → BrownianSample → ℝ)
    (K L : ℝ≥0) (hA : ∀ s sample,‖A s sample‖≤K) (hL : LipschitzWith L F) (s : ℝ) (sample : BrownianSample) :
    ‖signedControlGapSource F m x A s sample‖≤|m| /2*((K:ℝ)^2+((K:ℝ)+L)^2) := by
  let Qx := signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
    (scalarControlledState m x A s.toNNReal sample)
  have hQ : ‖Qx‖≤L := norm_signedHeatLogDx_exp_le hF L hL m _ _ hm
  have hsub : ‖A s sample-Qx‖≤(K:ℝ)+L :=
    (norm_sub_le _ _).trans (add_le_add (hA s sample) hQ)
  unfold signedControlGapSource
  rw [norm_mul,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖A s sample^2-(A s sample-Qx)^2‖ ≤ ‖A s sample‖^2+‖A s sample-Qx‖^2 := by
      convert! norm_sub_le (A s sample^2) ((A s sample-Qx)^2) using 1 <;> simp [Real.norm_eq_abs]
    _ ≤ _ := by gcongr;exact hA s sample

theorem signedControl_squareGap_cropped {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m≠0) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A)
    (T : ℝ≥0) (hT : (T : ℝ)<1) :
    (∫ sample,signedHeatLog (fun y=>Real.exp (m*F y)) m (1-T)
      (scalarControlledState m x A T sample)-
      (∫ s in 0..(T : ℝ),signedControlGapSource F m x A s sample) ∂canonicalBrownianMeasure)=
      signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x := by
  let D := fun y=>Real.exp (m*F y)
  let δ := (1-(T : ℝ))/2
  have hδ : 0<δ := by dsimp [δ];linarith
  have hcap : (T : ℝ)+δ≤1 := by dsimp [δ];linarith
  let f := cappedSignedHeatLog D m 1 T δ
  have hD := hF.expHeatDatum m
  have hp : ∀ v y,gaussianHeatFlow D v y≠0 :=
    fun v y=>(gaussianHeatFlow_exp_pos hF m v y).ne'
  obtain ⟨hf,ht,hs,hdt,hdx,hxx⟩ := cappedSignedHeatLog_ito_regular hD m 1 T δ hm hδ hcap hp
  obtain ⟨L,hL⟩ := hF.lipschitz
  obtain ⟨K,hK⟩ := hA.bounded
  have hfb : ∀ s∈Icc (0 : ℝ) T,∀ y,‖itoSpaceDerivative f s y‖≤L := by
    intro s _ y
    rw [(cappedSignedHeatLog_ito_derivatives hD m 1 T δ s y hm hδ hcap hp).2.1]
    exact norm_signedHeatLogDx_exp_le hF L hL m _ y hm
  have hcost : ∀ sample,IntervalIntegrable (fun s=>signedControlGapSource F m x A s sample) volume 0 T := by
    intro sample
    apply (intervalIntegrable_const (c:=|m| /2*((K:ℝ)^2+((K:ℝ)+L)^2))).mono_fun'
      ((measurable_signedControlGapSource hF m x A hA).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact .of_forall (fun s=>norm_signedControlGapSource_le hF m x hm A K L hK hL s sample)
  have hic := integrable_bounded_intervalIntegral canonicalBrownianMeasure
    (signedControlGapSource F m x A) (measurable_signedControlGapSource hF m x A hA)
    (|m| /2*((K:ℝ)^2+((K:ℝ)+L)^2))
    (norm_signedControlGapSource_le hF m x hm A K L hK hL) 0 T T.coe_nonneg
  have hgen : ∀ sample,∀ s∈Icc (0 : ℝ) T,
      hjbGenerator (scalarControlledState m x A) (scalarControlDrift m A) 1 f s sample=
        signedControlGapSource F m x A s sample := by
    intro sample s hs
    unfold hjbGenerator
    simp only [one_pow,mul_one,scalarControlDrift,Real.coe_toNNReal _ hs.1]
    exact cappedSignedHeatLog_generator hD m 1 T δ s _ (A s sample) hm hδ hcap hp hs.2
  have he0 (sample : BrownianSample) : f 0 (scalarControlledState m x A 0 sample)=signedHeatLog D m 1 x := by
    rw [scalarControlledState_zero]
    simp only [f,cappedSignedHeatLog,hjbTimeCap_of_le _ _ _ T.coe_nonneg,sub_zero]
  have heT (sample : BrownianSample) : f T (scalarControlledState m x A T sample)=
      signedHeatLog D m (1-T) (scalarControlledState m x A T sample) := by
    simp only [f,cappedSignedHeatLog,hjbTimeCap_of_le _ _ _ (le_refl (T : ℝ))]
  have hi0 : Integrable (fun sample=>f 0 (scalarControlledState m x A 0 sample)) canonicalBrownianMeasure := by
    simp_rw [he0]
    exact integrable_const _
  have hiT : Integrable (fun sample=>f T (scalarControlledState m x A T sample)) canonicalBrownianMeasure := by
    simp_rw [heT]
    exact integrable_lipschitz_scalarControlledState m x A hA T _ L
      (lipschitz_signedHeatLog_exp hF L hL m (1-T) hm)
  have hh := hjb_control_expected_eq (boundedDriftItoCharacteristics_scalarControlledState m x A hA)
    f hf ht hs hdt hdx hxx 0 T (show (0 : ℝ≥0)≤T from zero_le) L hfb (signedControlGapSource F m x A)
    hcost hgen hi0 hiT hic
  simpa only [NNReal.coe_zero,heT,he0,integral_const,probReal_univ,one_smul] using hh

end FourPapersCommon
