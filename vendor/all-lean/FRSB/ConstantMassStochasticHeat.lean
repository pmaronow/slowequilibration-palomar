module
public import FRSB.BackwardsConstantTime
public import FRSB.InteriorTimeCap
public import FRSB.ItoStochasticTools
public import FRSB.ZeroDriftBrownian

@[expose] public section

/-! Literal stochastic Cole--Hopf heat identity on a constant-CDF open
cell. The final coefficient and observable contain no time cap. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped ContDiff Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000

theorem constantMassHeatStochasticLeftSums (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (l r : ℝ≥0)
    (hl : a < (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) < b) (y : ℝ) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t sample => m * Real.exp (m * parisiPotential β μ
          ((l : ℝ) + t,zeroDriftBrownian β l y t sample)) *
            parisiGradient β μ ((l : ℝ) + t,zeroDriftBrownian β l y t sample))
        (r-l) (n+1) (r-l)) atTop
      (fun sample => Real.exp (m * parisiPotential β μ
        ((r : ℝ),zeroDriftBrownian β l y (r-l) sample)) -
          Real.exp (m * parisiPotential β μ ((l : ℝ),y))) := by
  let clamp : ℝ → ℝ := fun t => projIcc (0 : ℝ) 1 (by norm_num) t
  let u : ℝ → ℝ → ℝ := fun t x => Real.exp (m * parisiPotential β μ (clamp t,x))
  let ut : ℝ → ℝ → ℝ := fun t x => -(β^2*m/2)*u t x*
    (parisiHessian β μ (clamp t,x)+m*parisiGradient β μ (clamp t,x)^2)
  let ux : ℝ → ℝ → ℝ := fun t x => m*u t x*parisiGradient β μ (clamp t,x)
  let uxx : ℝ → ℝ → ℝ := fun t x => m*u t x*
    (parisiHessian β μ (clamp t,x)+m*parisiGradient β μ (clamp t,x)^2)
  let f := interiorCappedTest u a l r b
  let fR := timeShiftTest f l
  let X := zeroDriftBrownian β l y
  let T := r-l
  have hcl : Continuous clamp := by
    exact continuous_subtype_val.comp continuous_projIcc
  have hmap : Continuous (fun p : ℝ × ℝ => (clamp p.1,p.2)) :=
    (hcl.comp continuous_fst).prodMk continuous_snd
  have hU : Continuous (fun p : ℝ × ℝ => u p.1 p.2) :=
    Real.continuous_exp.comp (((continuous_parisiPotential β μ).comp hmap).const_mul m)
  have hB := (continuous_parisiGradient β μ).comp hmap
  have hC := (continuous_parisiHessian_all β μ).comp hmap
  have hUt : Continuous (fun p : ℝ × ℝ => ut p.1 p.2) :=
    (hU.const_mul _).mul (hC.add ((hB.pow 2).const_mul m))
  have hUx : Continuous (fun p : ℝ × ℝ => ux p.1 p.2) := (hU.const_mul m).mul hB
  have hUxx : Continuous (fun p : ℝ × ℝ => uxx p.1 p.2) :=
    (hU.const_mul m).mul (hC.add ((hB.pow 2).const_mul m))
  have hcm (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := (projIcc (0 : ℝ) 1 (by norm_num) t).property
  have hce (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
    simp only [clamp,projIcc_of_mem (by norm_num) ht,Subtype.coe_mk]
  have hut : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t := by
    intro t ht x
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩
    have hh := ((hasDerivAt_parisiPotential_constantCDF_time β hβ μ ha hab hb hc ht x).const_mul m).exp
    have he : (fun s => u s x) =ᶠ[𝓝 t] (fun s => Real.exp (m*parisiPotential β μ (s,x))) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      dsimp only [u]
      rw [hce s ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩]
    convert hh.congr_of_eventuallyEq he using 1
    dsimp only [ut,u]
    rw [hce t ht01]
    ring
  have hux : ∀ t x, HasDerivAt (u t) (ux t x) x := by
    intro t x
    have hh := ((hasDerivAt_parisiPotential_spatial_all β μ (clamp t) x (hcm t)).const_mul m).exp
    convert hh using 1
    dsimp only [u,ux]
    ring
  have huxx : ∀ t x, HasDerivAt (ux t) (uxx t x) x := by
    intro t x
    have hh := ((hux t x).const_mul m).mul
      (hasDerivAt_parisiGradient_spatial_all β μ (clamp t) x)
    convert hh using 1
    dsimp only [ux,uxx]
    ring
  have hC2 (t : ℝ) : ContDiff ℝ 2 (u t) :=
    ((contDiff_const.mul (contDiff_parisiPotential_spatial β μ (clamp t) (hcm t))).exp).of_le (by simp)
  obtain ⟨hfc,hft,hfs,hfdt,hfx,hfxx⟩ := interiorCappedTest_regular u ut ux uxx a l r b
    hl (NNReal.coe_le_coe.mpr hlr) hr hU hUt hUx hUxx hut hux huxx hC2
  obtain ⟨hRc,hRt,hRs,hRdt,hRx,hRxx⟩ := timeShiftTest_regular f l hfc hft hfs hfdt hfx hfxx
  have hwindow {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) :
      (l : ℝ)+t ∈ Icc (l : ℝ) (r : ℝ) := by
    have hT : (T : ℝ)=(r : ℝ)-l := NNReal.coe_sub hlr
    constructor <;> linarith [ht.1,ht.2]
  have hwindow01 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) :
      (l : ℝ)+t ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.trans (hl.le.trans (hwindow ht).1),(hwindow ht).2.trans (hr.le.trans hb)⟩
  have hgen : ∀ sample, ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      hjbGenerator X (fun _ _ => 0) β fR t sample = (0 : ℝ) := by
    intro sample t ht
    have htw := hwindow ht
    unfold hjbGenerator
    rw [timeShiftTest_timeDerivative f l t _ hft,
      timeShiftTest_spaceDerivative,timeShiftTest_spaceSecondDerivative,
      interiorCappedTest_timeDerivative u ut a l r b hl (NNReal.coe_le_coe.mpr hlr) hr hut,
      interiorCappedTest_spaceDerivative u ux hux,
      interiorCappedTest_spaceSecondDerivative u ux uxx hux huxx,
      interiorTimeCap_eq _ _ _ _ _ htw,interiorTimeCapD_eq _ _ _ _ _ htw]
    dsimp only [ut,uxx]
    ring
  have hconv := ito_stochastic_leftSums_source
    (boundedDriftItoCharacteristics_zeroDriftBrownian β l y) fR hRc hRt hRs hRdt hRx hRxx T
    (fun _ _ => 0) hgen
  have hleft (n : ℕ) (sample : BrownianSample) :
      uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t sample => itoSpaceDerivative fR t (X t sample)) T (n+1) T sample =
      uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t sample => m*Real.exp (m*parisiPotential β μ ((l : ℝ)+t,X t sample))*
          parisiGradient β μ ((l : ℝ)+t,X t sample)) T (n+1) T sample := by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal,uniformAdaptedMartingaleLeftSumProcess_terminal]
    apply Finset.sum_congr rfl
    intro i hi
    have hiT : (uniformPartitionTime T (n+1) i : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
      uniformPartitionTime_mem_Icc_of_le T (Nat.succ_pos n) (Nat.le_of_lt (Finset.mem_range.mp hi))
    rw [timeShiftTest_spaceDerivative,interiorCappedTest_spaceDerivative u ux hux,
      interiorTimeCap_eq _ _ _ _ _ (hwindow hiT)]
    dsimp only [ux,u]
    rw [hce _ (hwindow01 hiT)]
  have heval (t : ℝ≥0) (ht : t ∈ Icc 0 T) (sample : BrownianSample) :
      fR t (X t sample) = Real.exp (m*parisiPotential β μ ((l : ℝ)+t,X t sample)) := by
    have htR : (t : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := ⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩
    dsimp only [fR,timeShiftTest,f,interiorCappedTest,u]
    rw [interiorTimeCap_eq _ _ _ _ _ (hwindow htR),hce _ (hwindow01 htR)]
  have hconv' := hconv.congr_left (fun n => .of_forall (hleft n))
  apply TendstoInMeasure.congr_right _ hconv'
  exact .of_forall fun sample => by
    have hTe := heval T ⟨by positivity,le_rfl⟩ sample
    have h0e := heval 0 ⟨by positivity,by positivity⟩ sample
    simp only [NNReal.coe_zero,add_zero,X,zeroDriftBrownian_initial] at h0e
    dsimp only at hTe h0e ⊢
    rw [hTe,zeroDriftBrownian_initial,h0e,intervalIntegral.integral_zero,sub_zero]
    simp only [add_zero,NNReal.coe_sub hlr,X,T]
    rw [show (l : ℝ)+((r : ℝ)-l)=(r : ℝ) by ring]

end FRSB
