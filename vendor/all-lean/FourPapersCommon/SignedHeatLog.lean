module
public import FRSB.BackwardHeatTest
public import FourPapersCommon.VariableItoExpectation

@[expose] public section

/-! The signed logarithm of an actual scalar Gaussian heat integral. All
spatial and time derivatives, including the signed Hamilton--Jacobi equation,
are derived from the Gaussian integral. No control representation is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper StochasticCalculus FRSB
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000

def signedHeatLog (D : ℝ → ℝ) (m v x : ℝ) : ℝ := Real.log (gaussianHeatFlow D v x)/m

def signedHeatLogDx (D : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  gaussianHeatFlow (deriv D) v x/(m*gaussianHeatFlow D v x)

def signedHeatLogDxx (D : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  (gaussianHeatFlow (iteratedDeriv 2 D) v x/gaussianHeatFlow D v x-
    (gaussianHeatFlow (deriv D) v x/gaussianHeatFlow D v x)^2)/m

def signedHeatLogDv (D : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  gaussianHeatFlow (iteratedDeriv 2 D) v x/(2*m*gaussianHeatFlow D v x)

theorem hasDerivAt_signedHeatLog_spatial {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m v x : ℝ) (hp : gaussianHeatFlow D v x≠0) :
    HasDerivAt (signedHeatLog D m v) (signedHeatLogDx D m v x) x := by
  have hh := ((hasDerivAt_gaussianHeatFlow_spatial hD v x).log hp).div_const m
  convert hh using 1
  · rfl
  · unfold signedHeatLogDx
    ring

theorem hasDerivAt_signedHeatLogDx {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m v x : ℝ) (hm : m≠0) (hp : gaussianHeatFlow D v x≠0) :
    HasDerivAt (signedHeatLogDx D m v) (signedHeatLogDxx D m v x) x := by
  have hh := (hasDerivAt_gaussianHeatFlow_first_spatial hD v x).div
    ((hasDerivAt_gaussianHeatFlow_spatial hD v x).const_mul m) (mul_ne_zero hm hp)
  convert hh using 1
  · rfl
  · unfold signedHeatLogDxx
    field_simp <;> ring

theorem hasDerivAt_signedHeatLog_variance {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m : ℝ) {v : ℝ} (hv : 0<v) (x : ℝ) (hp : gaussianHeatFlow D v x≠0) :
    HasDerivAt (fun w=>signedHeatLog D m w x) (signedHeatLogDv D m v x) v := by
  have hh := ((hasDerivAt_gaussianHeatFlow_variance hD hv x).log hp).div_const m
  convert hh using 1
  · rfl
  · unfold signedHeatLogDv
    ring

theorem signedHeatLog_heat_generator (D : ℝ → ℝ) (m v x : ℝ)
    (hm : m≠0) (hp : gaussianHeatFlow D v x≠0) :
    -signedHeatLogDv D m v x+(1/2:ℝ)*signedHeatLogDxx D m v x+
      (m/2)*(signedHeatLogDx D m v x)^2=0 := by
  unfold signedHeatLogDv signedHeatLogDxx signedHeatLogDx
  field_simp
  ring

theorem continuous_signedHeatLog_jets {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m : ℝ) (hp : ∀ v x,gaussianHeatFlow D v x≠0) :
    Continuous (fun p : ℝ × ℝ=>signedHeatLog D m p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ=>signedHeatLogDx D m p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ=>signedHeatLogDxx D m p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ=>signedHeatLogDv D m p.1 p.2) := by
  have hd0 := continuous_gaussianHeatFlow hD
  have hd1 : Continuous (fun p : ℝ × ℝ=>gaussianHeatFlow (deriv D) p.1 p.2) := by
    simpa only [iteratedDeriv_one] using continuous_gaussianHeatFlow_jet hD (j:=1) (by norm_num)
  have hd2 := continuous_gaussianHeatFlow_jet hD (j:=2) (by norm_num)
  refine ⟨(hd0.log (fun p=>hp p.1 p.2)).div_const m,?_,?_,?_⟩
  · exact (hd1.div hd0 (fun p=>hp p.1 p.2)).div_const m |>.congr
      (fun p=>by dsimp [signedHeatLogDx];ring)
  · exact ((hd2.div hd0 (fun p=>hp p.1 p.2)).sub
      ((hd1.div hd0 (fun p=>hp p.1 p.2)).pow 2)).div_const m
  · exact (hd2.div hd0 (fun p=>hp p.1 p.2)).div_const (2*m) |>.congr
      (fun p=>by dsimp [signedHeatLogDv];ring)

def cappedSignedHeatLog (D : ℝ → ℝ) (m b c δ t x : ℝ) : ℝ :=
  signedHeatLog D m (b-hjbTimeCap c δ t) x

theorem hasDerivAt_cappedSignedHeatLog_time {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m b c δ t x : ℝ) (hδ : 0<δ) (hcb : c+δ≤b)
    (hp : ∀ v x,gaussianHeatFlow D v x≠0) :
    HasDerivAt (fun s=>cappedSignedHeatLog D m b c δ s x)
      (-hjbTimeCapD c δ t*signedHeatLogDv D m (b-hjbTimeCap c δ t) x) t := by
  have hv : 0<b-hjbTimeCap c δ t :=
    sub_pos.mpr ((hjbTimeCap_lt c hδ t).trans_le hcb)
  have hh := (hasDerivAt_signedHeatLog_variance hD m hv x (hp _ _)).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_hjbTimeCap c hδ t))
  convert hh using 1
  · rfl
  · ring

theorem cappedSignedHeatLog_ito_derivatives {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m b c δ t x : ℝ) (hm : m≠0) (hδ : 0<δ) (hcb : c+δ≤b)
    (hp : ∀ v x,gaussianHeatFlow D v x≠0) :
    itoTimeDerivative (cappedSignedHeatLog D m b c δ) t x=
      -hjbTimeCapD c δ t*signedHeatLogDv D m (b-hjbTimeCap c δ t) x ∧
    itoSpaceDerivative (cappedSignedHeatLog D m b c δ) t x=
      signedHeatLogDx D m (b-hjbTimeCap c δ t) x ∧
    itoSpaceSecondDerivative (cappedSignedHeatLog D m b c δ) t x=
      signedHeatLogDxx D m (b-hjbTimeCap c δ t) x := by
  refine ⟨(hasDerivAt_cappedSignedHeatLog_time hD m b c δ t x hδ hcb hp).deriv,
    (hasDerivAt_signedHeatLog_spatial hD m _ x (hp _ _)).deriv,?_⟩
  unfold itoSpaceSecondDerivative
  have he : deriv (cappedSignedHeatLog D m b c δ t)=
      signedHeatLogDx D m (b-hjbTimeCap c δ t) := by
    funext y
    exact (hasDerivAt_signedHeatLog_spatial hD m _ y (hp _ _)).deriv
  rw [he]
  exact (hasDerivAt_signedHeatLogDx hD m _ x hm (hp _ _)).deriv

theorem cappedSignedHeatLog_ito_regular {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m b c δ : ℝ) (hm : m≠0) (hδ : 0<δ) (hcb : c+δ≤b)
    (hp : ∀ v x,gaussianHeatFlow D v x≠0) :
    Continuous (fun p : ℝ × ℝ=>cappedSignedHeatLog D m b c δ p.1 p.2) ∧
    (∀ x,Differentiable ℝ (fun s=>cappedSignedHeatLog D m b c δ s x)) ∧
    (∀ s,ContDiff ℝ 2 (cappedSignedHeatLog D m b c δ s)) ∧
    Continuous (fun p : ℝ × ℝ=>itoTimeDerivative (cappedSignedHeatLog D m b c δ) p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ=>itoSpaceDerivative (cappedSignedHeatLog D m b c δ) p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ=>itoSpaceSecondDerivative (cappedSignedHeatLog D m b c δ) p.1 p.2) := by
  obtain ⟨hf,hx,hxx,hv⟩ := continuous_signedHeatLog_jets hD m hp
  have hmap : Continuous (fun p : ℝ × ℝ=>(b-hjbTimeCap c δ p.1,p.2)) := by fun_prop
  refine ⟨hf.comp hmap,fun x t=>(hasDerivAt_cappedSignedHeatLog_time hD m b c δ t x hδ hcb hp).differentiableAt,
    ?_,?_,?_,?_⟩
  · intro s
    exact ((contDiff_gaussianHeatFlow_spatial hD _).log (fun x=>hp _ x)).div_const m
  · have he := funext (fun p : ℝ × ℝ=>
      (cappedSignedHeatLog_ito_derivatives hD m b c δ p.1 p.2 hm hδ hcb hp).1)
    rw [he]
    exact ((continuous_hjbTimeCapD c δ).comp continuous_fst).neg.mul (hv.comp hmap)
  · have he := funext (fun p : ℝ × ℝ=>
      (cappedSignedHeatLog_ito_derivatives hD m b c δ p.1 p.2 hm hδ hcb hp).2.1)
    rw [he]
    exact hx.comp hmap
  · have he := funext (fun p : ℝ × ℝ=>
      (cappedSignedHeatLog_ito_derivatives hD m b c δ p.1 p.2 hm hδ hcb hp).2.2)
    rw [he]
    exact hxx.comp hmap

theorem cappedSignedHeatLog_generator {D : ℝ → ℝ} (hD : HeatC2Datum D)
    (m b c δ t x u : ℝ) (hm : m≠0) (hδ : 0<δ) (hcb : c+δ≤b)
    (hp : ∀ v x,gaussianHeatFlow D v x≠0) (ht : t≤c) :
    itoTimeDerivative (cappedSignedHeatLog D m b c δ) t x+
      itoSpaceDerivative (cappedSignedHeatLog D m b c δ) t x*(m*u)+
      (1/2:ℝ)*itoSpaceSecondDerivative (cappedSignedHeatLog D m b c δ) t x=
      m/2*(u^2-(u-signedHeatLogDx D m (b-t) x)^2) := by
  obtain ⟨hdt,hdx,hxx⟩ := cappedSignedHeatLog_ito_derivatives hD m b c δ t x hm hδ hcb hp
  rw [hdt,hdx,hxx,hjbTimeCap_of_le c δ t ht]
  have hcap : hjbTimeCapD c δ t=1 := by simp [hjbTimeCapD,ht]
  rw [hcap]
  have hh := signedHeatLog_heat_generator D m (b-t) x hm (hp _ _)
  nlinarith

end FourPapersCommon
