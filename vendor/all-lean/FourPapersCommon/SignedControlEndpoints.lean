module
public import FourPapersCommon.SignedControlVerification
public import FourPapersCommon.ScalarControlContinuity
public import FRSB.StochasticCrops

@[expose] public section

/-! Closing signed scalar Brownian verification at terminal variance zero.
The logarithmic heat observable converges in L¹ by its genuine uniform heat
modulus and the actual state increment estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus FRSB
open scoped Topology NNReal
namespace FourPapersCommon
open Paper ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000

theorem tendsto_integral_bounded_primitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℝ → Ω → ℝ)
    (hf : Measurable (Function.uncurry f)) (C : ℝ) (hC : ∀ s sample,‖f s sample‖≤C)
    (t : ℕ → ℝ) (ht : ∀ n,t n∈Icc (0 : ℝ) 1) (hlim : Tendsto t atTop (𝓝 1)) :
    Tendsto (fun n=>∫ sample,(∫ s in 0..t n,f s sample) ∂P) atTop
      (𝓝 (∫ sample,(∫ s in 0..(1 : ℝ),f s sample) ∂P)) := by
  have hM : 0 ≤ max C 0 := le_max_right _ _
  apply tendsto_integral_of_dominated_convergence (fun _=>max C 0)
  · intro n
    exact (integrable_bounded_intervalIntegral P f hf C hC 0 (t n) (ht n).1).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact .of_forall (fun sample=>by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a:=(0 : ℝ)) (b:=t n) (C:=max C 0) (f:=fun s=>f s sample)
        (fun s _=>(hC s sample).trans (le_max_left C 0))
      have hn : |t n-0|≤1 := by rw [sub_zero,abs_of_nonneg (ht n).1];exact (ht n).2
      exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hM))
  · apply Eventually.of_forall
    intro sample
    have hInt (a b : ℝ) : IntervalIntegrable (fun s=>f s sample) volume a b :=
      (intervalIntegrable_const (c:=C)).mono_fun'
        (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (.of_forall (fun s=>hC s sample))
    exact (intervalIntegral.continuous_primitive hInt (0 : ℝ)).continuousAt.tendsto.comp hlim

theorem tendsto_signedHeatLog_control_endpoint {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m≠0) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop (𝓝 1)) :
    Tendsto (fun n=>∫ sample,signedHeatLog (fun y=>Real.exp (m*F y)) m (1-t n)
      (scalarControlledState m x A (t n) sample) ∂canonicalBrownianMeasure) atTop
      (𝓝 (∫ sample,F (scalarControlledState m x A 1 sample) ∂canonicalBrownianMeasure)) := by
  obtain ⟨L,hL⟩ := hF.lipschitz
  let Q := fun n sample=>signedHeatLog (fun y=>Real.exp (m*F y)) m (1-t n)
    (scalarControlledState m x A (t n) sample)
  let G := fun sample=>F (scalarControlledState m x A 1 sample)
  have hiQ (n : ℕ) : Integrable (Q n) canonicalBrownianMeasure :=
    integrable_lipschitz_scalarControlledState m x A hA (t n) _ L
      (lipschitz_signedHeatLog_exp hF L hL m _ hm)
  have hiG : Integrable G canonicalBrownianMeasure :=
    integrable_lipschitz_scalarControlledState m x A hA 1 F L hL
  have hbound (n : ℕ) (sample : BrownianSample) : |Q n sample-G sample|≤
      coleHopfModulus m L ((1 : ℝ)-(t n : ℝ)).toNNReal+
        (L:ℝ)*|scalarControlledState m x A (t n) sample-scalarControlledState m x A 1 sample| := by
    have hh := abs_coleHopf_sub_self_le hF.smooth.continuous.measurable
      (fun y z=>by simpa only [Real.dist_eq] using hL.dist_le_mul z y) m
      ((1 : ℝ)-(t n : ℝ)).toNNReal (scalarControlledState m x A (t n) sample)
    have hFdist := hL.dist_le_mul (scalarControlledState m x A (t n) sample)
      (scalarControlledState m x A 1 sample)
    simp only [Real.dist_eq] at hFdist
    have hs := abs_add_le
      (Q n sample-F (scalarControlledState m x A (t n) sample))
      (F (scalarControlledState m x A (t n) sample)-G sample)
    have he : Q n sample-G sample=(Q n sample-F (scalarControlledState m x A (t n) sample))+
        (F (scalarControlledState m x A (t n) sample)-G sample) := by ring
    rw [he]
    apply hs.trans
    apply add_le_add _ hFdist
    simpa only [Q,signedHeatLog_exp_eq_coleHopf _ _ _ _ hm] using hh
  have hnorm (n : ℕ) : ‖(∫ sample,Q n sample ∂canonicalBrownianMeasure)-
      (∫ sample,G sample ∂canonicalBrownianMeasure)‖≤coleHopfModulus m L ((1 : ℝ)-(t n : ℝ)).toNNReal+
        (L:ℝ)*(∫ sample,|scalarControlledState m x A (t n) sample-
          scalarControlledState m x A 1 sample| ∂canonicalBrownianMeasure) := by
    have hiD := ((integrable_scalarControlledState m x A hA (t n)).sub
      (integrable_scalarControlledState m x A hA 1)).abs
    rw [←integral_sub (hiQ n) hiG]
    have hh := integral_mono ((hiQ n).sub hiG).abs
      ((integrable_const (coleHopfModulus m L ((1 : ℝ)-(t n : ℝ)).toNNReal)).add (hiD.const_mul (L:ℝ)))
      (hbound n)
    have hn := norm_integral_le_integral_norm (μ:=canonicalBrownianMeasure)
      (fun sample=>Q n sample-G sample)
    simp only [Real.norm_eq_abs] at hn
    apply hn.trans
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    have hadd := integral_add (integrable_const
      (coleHopfModulus m L ((1 : ℝ)-(t n : ℝ)).toNNReal)) (hiD.const_mul (L:ℝ))
    simp only [Pi.add_apply, Pi.sub_apply] at hadd
    rw [hadd, integral_const, integral_const_mul] at hh
    simpa only [probReal_univ, one_smul] using hh
  have hv : Tendsto (fun n : ℕ=>(1 : ℝ)-(t n : ℝ)) atTop (𝓝 0) := by
    have hcoe : Tendsto (fun n=>(t n : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      (NNReal.continuous_coe.tendsto 1).comp ht
    have hh : Tendsto (fun n=>(1 : ℝ)-(t n : ℝ)) atTop (𝓝 ((1 : ℝ)-1)) :=
      tendsto_const_nhds.sub hcoe
    simpa only [sub_self] using hh
  have hmod := (tendsto_coleHopfModulus m L).comp hv
  have hstate := (tendsto_integral_abs_scalarControlledState_increment m x A hA 1).comp ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n=>norm_nonneg _) hnorm
  simpa only [Function.comp_apply, mul_zero,add_zero] using hmod.add (hstate.const_mul (L:ℝ))

theorem signedControl_squareGap_closed {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m≠0) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) :
    (∫ sample,F (scalarControlledState m x A 1 sample)-
      (∫ s in 0..(1 : ℝ),signedControlGapSource F m x A s sample) ∂canonicalBrownianMeasure)=
      signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x := by
  let t := rightCellCrop (0 : ℝ) 1
  have ht : Tendsto t atTop (𝓝 1) := by
    simpa only [Real.toNNReal_one] using tendsto_rightCellCrop (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1)
  have htn (n : ℕ) : (t n : ℝ)<1 := (cellCrop_bounds (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1) n).2.2
  have htI (n : ℕ) : (t n : ℝ)∈Icc (0 : ℝ) 1 := ⟨(t n).coe_nonneg,(htn n).le⟩
  obtain ⟨L,hL⟩ := hF.lipschitz
  obtain ⟨K,hK⟩ := hA.bounded
  have hbound := norm_signedControlGapSource_le hF m x hm A K L hK hL
  have hcost := tendsto_integral_bounded_primitive canonicalBrownianMeasure
    (signedControlGapSource F m x A) (measurable_signedControlGapSource hF m x A hA)
    (|m| /2*((K:ℝ)^2+((K:ℝ)+L)^2)) hbound (fun n=>(t n : ℝ)) htI
    ((NNReal.continuous_coe.tendsto 1).comp ht)
  have hterminal := tendsto_signedHeatLog_control_endpoint hF m x hm A hA t ht
  have hiF := integrable_lipschitz_scalarControlledState m x A hA 1 F L hL
  have hiCost := integrable_bounded_intervalIntegral canonicalBrownianMeasure
    (signedControlGapSource F m x A) (measurable_signedControlGapSource hF m x A hA)
    (|m| /2*((K:ℝ)^2+((K:ℝ)+L)^2)) hbound 0 1 (by norm_num)
  rw [integral_sub hiF hiCost]
  have he (n : ℕ) : (∫ sample,signedHeatLog (fun y=>Real.exp (m*F y)) m (1-t n)
      (scalarControlledState m x A (t n) sample) ∂canonicalBrownianMeasure)-
      (∫ sample,(∫ s in 0..(t n : ℝ),signedControlGapSource F m x A s sample) ∂canonicalBrownianMeasure)=
      signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x := by
    rw [←integral_sub
      (integrable_lipschitz_scalarControlledState m x A hA (t n) _ L
        (lipschitz_signedHeatLog_exp hF L hL m _ hm))
      (integrable_bounded_intervalIntegral canonicalBrownianMeasure _
        (measurable_signedControlGapSource hF m x A hA) _ hbound 0 (t n) (t n).coe_nonneg)]
    exact signedControl_squareGap_cropped hF m x hm A hA (t n) (htn n)
  exact tendsto_nhds_unique (hterminal.sub hcost) (tendsto_const_nhds.congr' (.of_forall (fun n=>(he n).symm)))

end FourPapersCommon
