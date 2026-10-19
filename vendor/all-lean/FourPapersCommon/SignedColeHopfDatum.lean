module
public import FourPapersCommon.SignedHeatLog

@[expose] public section

/-! Concrete scalar terminal regularity suffices for the signed Gaussian
Cole--Hopf test. In particular, the exponential heat datum and the global
logarithmic-gradient bound are proved rather than supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FRSB
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000

structure SignedScalarDatum (A : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 A
  lipschitz : ∃ L : ℝ≥0,LipschitzWith L A
  second_bound : ∃ K : ℝ,∀ x,|iteratedDeriv 2 A x|≤K

theorem SignedScalarDatum.linearGrowth {A : ℝ → ℝ} (hA : SignedScalarDatum A) :
    HasLinearGrowth A := by
  obtain ⟨L,hL⟩ := hA.lipschitz
  exact HasLinearGrowth.of_lipschitz (fun x y=>by
    simpa only [Real.dist_eq] using hL.dist_le_mul y x)

theorem SignedScalarDatum.expHeatDatum {A : ℝ → ℝ} (hA : SignedScalarDatum A) (m : ℝ) :
    HeatC2Datum (fun x=>Real.exp (m*A x)) := by
  obtain ⟨L,hL⟩ := hA.lipschitz
  obtain ⟨K,hK⟩ := hA.second_bound
  have hfirst : ∀ x,|deriv A x|≤L := fun x=>by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀:=x) hL
  have hg0 := hA.linearGrowth.exp_mul m
  have hg1 : HasExpGrowth (deriv A) := HasExpGrowth.of_bounded hfirst
  have hg2 : HasExpGrowth (iteratedDeriv 2 A) := HasExpGrowth.of_bounded hK
  have hdiff : Differentiable ℝ A := hA.smooth.differentiable (by norm_num)
  have hd : deriv (fun x=>Real.exp (m*A x))=
      fun x=>m*deriv A x*Real.exp (m*A x) := by
    funext x
    simpa only [mul_comm] using ((hdiff x).hasDerivAt.const_mul m).exp.deriv
  have hdA (x : ℝ) : HasDerivAt (deriv A) (iteratedDeriv 2 A x) x := by
    have hh := (hA.smooth.differentiable_iteratedDeriv 1 (by norm_num) x).hasDerivAt
    convert! hh using 1 <;> simp only [iteratedDeriv_one,iteratedDeriv_succ,iteratedDeriv_zero]
  have hdd : iteratedDeriv 2 (fun x=>Real.exp (m*A x))=
      fun x=>(m*iteratedDeriv 2 A x+(m*deriv A x)^2)*Real.exp (m*A x) := by
    funext x
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hd]
    have hh := ((hdA x).const_mul m).mul (((hdiff x).hasDerivAt.const_mul m).exp)
    convert! hh.deriv using 1 <;> ring
  refine ⟨(contDiff_const.mul hA.smooth).exp,fun j hj=>?_⟩
  rcases (show j=0 ∨ j=1 ∨ j=2 by omega) with rfl|rfl|rfl
  · simpa only [iteratedDeriv_zero] using hg0
  · simpa only [iteratedDeriv_one,hd] using (hg1.const_mul m).mul hg0
  · rw [hdd]
    exact ((hg2.const_mul m).add ((hg1.const_mul m).pow 2)).mul hg0

theorem gaussianHeatFlow_exp_pos {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (m v x : ℝ) : 0<gaussianHeatFlow (fun y=>Real.exp (m*A y)) v x :=
  integral_exp_mul_comp_add_pos hA.linearGrowth hA.smooth.continuous.measurable m _ x

theorem signedHeatLog_exp_eq_coleHopf (A : ℝ → ℝ) (m v x : ℝ) (hm : m≠0) :
    signedHeatLog (fun y=>Real.exp (m*A y)) m v x=coleHopf m v.toNNReal A x := by
  rw [signedHeatLog,coleHopf_of_ne hm]
  unfold gaussianHeatFlow
  ring

theorem lipschitz_signedHeatLog_exp {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (L : ℝ≥0) (hL : LipschitzWith L A) (m v : ℝ) (hm : m≠0) :
    LipschitzWith L (signedHeatLog (fun y=>Real.exp (m*A y)) m v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp_rw [signedHeatLog_exp_eq_coleHopf A m v _ hm,Real.dist_eq]
  exact abs_coleHopf_sub_le_of_lipschitz m hA.smooth.continuous.measurable
    (fun x y=>by simpa only [Real.dist_eq] using hL.dist_le_mul y x) _ y x

theorem norm_signedHeatLogDx_exp_le {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (L : ℝ≥0) (hL : LipschitzWith L A) (m v x : ℝ) (hm : m≠0) :
    ‖signedHeatLogDx (fun y=>Real.exp (m*A y)) m v x‖≤L := by
  have hd := hasDerivAt_signedHeatLog_spatial (hA.expHeatDatum m) m v x
    (gaussianHeatFlow_exp_pos hA m v x).ne'
  rw [←hd.deriv]
  exact norm_deriv_le_of_lipschitz (lipschitz_signedHeatLog_exp hA L hL m v hm)

theorem signedHeatLog_exp_terminal (A : ℝ → ℝ) (m x : ℝ) (hm : m≠0) :
    signedHeatLog (fun y=>Real.exp (m*A y)) m 0 x=A x := by
  rw [signedHeatLog_exp_eq_coleHopf A m 0 x hm]
  simp

theorem signedHeatLogDx_exp_eq_tilt {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (m v x : ℝ) (hm : m≠0) :
    signedHeatLogDx (fun y=>Real.exp (m*A y)) m v x=
      ∫ z,deriv A (x+z)*coleHopfQ m v.toNNReal A x z ∂gaussianReal 0 v.toNNReal := by
  have hd := hasDerivAt_signedHeatLog_spatial (hA.expHeatDatum m) m v x
    (gaussianHeatFlow_exp_pos hA m v x).ne'
  obtain ⟨L,hL⟩ := hA.lipschitz
  have hg : HasExpGrowth (deriv A) := HasExpGrowth.of_bounded (fun y=>by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀:=y) hL)
  have hd' := hasDerivAt_coleHopf
    (fun y=>(hA.smooth.differentiable (by norm_num) y).hasDerivAt) hA.linearGrowth hg
    (hA.smooth.continuous_deriv (by norm_num)).measurable hm v.toNNReal x
  have he : signedHeatLog (fun y=>Real.exp (m*A y)) m v=coleHopf m v.toNNReal A :=
    funext (fun y=>signedHeatLog_exp_eq_coleHopf A m v y hm)
  rw [he] at hd
  exact hd.unique hd'

end FourPapersCommon
