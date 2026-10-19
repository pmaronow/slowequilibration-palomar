module
public import FourPapersCommon.MixedSignedInitialLocal
public import Targets.ParisiStrictConvexity
public import Targets.Section5CompactTube
public import Paper.GaussianPositivity

@[expose] public section

/-! Strict zero-overlap scalar witnesses retain the actual positive frozen
Gaussian field. This closes the sign boundary of the negative initial half. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

 theorem retainedSignedInitial_origin_derivative_pos {k : ℕ}
    (s : RSBScheme k) (β h v b : ℝ) (hb : 0 < b) :
    0 < deriv (section5RetainedSignedInitialV s β h v b 0) 0 := by
  let A := parisiF s β (k+1)
  let A' := parisiFDeriv s β (k+1)
  let A'' := parisiFSecond s β (k+1)
  let S := stepD1 A A' 0 v
  have hA := parisiF_hasLinearGrowth s β (k+1)
  have hC2 := (parisiF_C2_props s β (k+1)).1
  have hAm := parisiF_measurable s β (k+1)
  have hA'm := (parisiF_C2_props s β (k+1)).2.1
  have hA''m := (parisiF_C2_props s β (k+1)).2.2
  have hS := hasParisiC2_parisiStep_nonneg (v:=v) (m:=0) le_rfl zero_le_one
    hC2 hA hAm hA'm hA''m
  have hSC : Continuous S := continuous_iff_continuousAt.mpr (fun x => (hS.2.1 x).continuousAt)
  have hSM : StrictMono S := strictMono_of_hasDerivAt_pos hS.2.1
    (stepD2_pos le_rfl hA hC2 hAm hA'm hA''m (parisiFSecond_pos s β (k+1)))
  obtain ⟨x,hx⟩ : ∃x:ℝ,S x ≠ 0 := by
    by_cases H:S 0=0
    · refine ⟨1,?_⟩
      have HH:=hSM (by norm_num : (0:ℝ)<1)
      rw [H] at HH
      exact HH.ne'
    · exact ⟨0,H⟩
  let g := fun z:ℝ => S (h+Real.sqrt b*z)^2
  have hg : Continuous g := (hSC.comp (by fun_prop)).pow 2
  have hgi : Integrable g (gaussianReal 0 1) := by
    apply (integrable_const (1:ℝ)).mono' hg.aestronglyMeasurable
    filter_upwards with z
    change ‖S (h+Real.sqrt b*z)^2‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have HH:=hS.abs_first_le_one (h+Real.sqrt b*z)
    change |S (h+Real.sqrt b*z)| ≤ 1 at HH
    exact (sq_le_one_iff_abs_le_one _).mpr HH
  have hgb : 0 < g ((x-h)/Real.sqrt b) := by
    have H: h+Real.sqrt b*((x-h)/Real.sqrt b)=x := by
      field_simp [(Real.sqrt_pos.mpr hb).ne']
      ring
    dsimp [g]
    rw [H]
    exact sq_pos_of_ne_zero hx
  have HP := Paper.gaussian_integral_pos_of_continuous_nonneg 0 1 (by norm_num)
    g hg hgi (fun z => sq_nonneg _) ((x-h)/Real.sqrt b) hgb
  rw [(hasDerivAt_section5RetainedSignedInitialV_zero s β h v b 0).deriv]
  simpa only [Real.sqrt_zero,zero_mul,add_zero,sub_zero,←pow_two,g,S,A,A',
    integral_const,probReal_univ,smul_eq_mul,one_mul] using HP

 theorem retainedSignedInitial_origin_scalar_witness {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (hβ : β ≠ 0) (hq : 0 < s.q 1)
    {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    ∃ell:ℝ,0 < 2*parisiF s β (k+2) h-
      section5RetainedSignedInitialV s β h (t*(β^2*s.q 1)) ((1-t)*(β^2*s.q 1)) 0 ell := by
  have hv : 0 ≤ t*(β^2*s.q 1) := mul_nonneg ht.1 (mul_nonneg (sq_nonneg _) hq.le)
  have hb : 0 < (1-t)*(β^2*s.q 1) :=
    mul_pos (sub_pos.mpr ht.2) (mul_pos (sq_pos_of_ne_zero hβ) hq)
  have HD := retainedSignedInitial_origin_derivative_pos s β h (t*(β^2*s.q 1))
    ((1-t)*(β^2*s.q 1)) hb
  obtain ⟨ell,HL⟩ := section5RetainedSignedInitialV_lambda_gain s β h
    (t*(β^2*s.q 1)) ((1-t)*(β^2*s.q 1)) 0 0
  have HZ := section5RetainedSignedInitialV_zero s β h hv hb.le le_rfl
    (show t*(β^2*s.q 1)+(1-t)*(β^2*s.q 1)+0=β^2*s.q 1 by ring)
  rw [HZ] at HL
  simp only [mul_zero,sub_zero] at HL
  refine ⟨ell,?_⟩
  have HH := sq_pos_of_pos HD
  nlinarith only [HL,HH]

 theorem continuous_retainedSignedInitial_origin_family {k : ℕ}
    (s : RSBScheme k) (β : ℝ) :
    Continuous (fun p:ℝ×ℝ×(ℝ×ℝ) =>
      section5RetainedSignedInitialCascade s β ((1-p.1)*(β^2*s.q 1)) 0
        (p.1*(β^2*s.q 1)) p.2.1 p.2.2) := by
  let Q := β^2*s.q 1
  let F := fun t ell xy => section5SignedInitialPrefix s β (t*Q) ell xy
  let D := fun t ell xy => section5SignedInitialPrefixD s β (t*Q) ell xy
  have HG : GTFrame.GoodFam (section5SignedInitialPrefix s β) (section5SignedInitialPrefixD s β) :=
    splitScalarCascade_good (fun j => section5Mass s 1 0 (k+2-j))
      (fun j => section5Variance s β 1 (k+2-j))
      (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
      (fun j => section5Variance_continuous s β 1 (k+2-j)) (k+2) (k+2)
  have HF : GTFrame.GoodFam F D := by
    constructor
    · exact HG.contF.comp (show Continuous (fun p:ℝ×ℝ×(ℝ×ℝ) => (p.1*Q,p.2.1,p.2.2)) by fun_prop)
    · exact HG.contD.comp (show Continuous (fun p:ℝ×ℝ×(ℝ×ℝ) => (p.1*Q,p.2.1,p.2.2)) by fun_prop)
    · exact fun t ell xy => HG.hasDeriv (t*Q) ell xy
    · exact fun t ell xy yz => HG.lipx (t*Q) ell xy yz
    · exact fun t ell xy => HG.bddD (t*Q) ell xy
  have H1 := finiteStep_good HF (m:=0) le_rfl
    (a:=fun t => Real.sqrt ((1-t)*Q)) (b:=fun t => Real.sqrt ((1-t)*Q))
    (by fun_prop) (by fun_prop)
  have H2 := finiteStep_good H1 (m:=0) le_rfl
    (a:=fun _ : ℝ => (0:ℝ)) (b:=fun _ : ℝ => (0:ℝ)) continuous_const continuous_const
  convert H2.contF using 1
  funext p
  simp [section5RetainedSignedInitialCascade,section5RetainedInitialPrefix,
    GTFrame.finiteStep,GTFrame.step0,F,Q]

end FourPapersCommon
