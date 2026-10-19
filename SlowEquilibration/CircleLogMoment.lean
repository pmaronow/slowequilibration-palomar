-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicircleWholeLine
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The genuine second circle Fourier moment of a logarithmic pole on the
unit circle, derived from Mathlib's actual Poisson representation. -/

@[expose] public section
namespace SlowEquilibration.CircleLogMoment

noncomputable section
open MeasureTheory Set Function Filter Real Complex Metric
open scoped Topology Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma unit_re_im_sq {z : ℂ} (hz : ‖z‖=1) : z.re^2+z.im^2=1 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz] at h
  simpa only [Complex.normSq_apply,pow_two,one_pow,mul_one] using h

lemma unit_re_sq_le {z : ℂ} (hz : ‖z‖=1) : z.re^2 ≤ 1 := by
  nlinarith [unit_re_im_sq hz,sq_nonneg z.im]

def poissonDen (r c : ℝ) : ℝ := 1-2*r*c+r^2

def secondDen (r c : ℝ) : ℝ := (1+r^2)^2-4*r^2*c^2

def secondKernel (r : ℝ) (z : ℂ) : ℝ := (2*z.re^2-1-r^2)/secondDen r z.re

lemma poissonDen_pos {r c : ℝ} (hr : |r|<1) (hc : c^2 ≤ 1) : 0 < poissonDen r c := by
  have habs : |c| ≤ 1 := by nlinarith [sq_abs c,sq_nonneg (|c|-1)]
  have hr1 : r^2<1 := by nlinarith [sq_abs r,sq_nonneg (|r|+1),abs_nonneg r]
  have hc1 : -1 ≤ c ∧ c ≤ 1 := abs_le.mp habs
  unfold poissonDen
  have hn : 0 ≤ (r-c)^2 := sq_nonneg (r-c)
  by_cases he : c^2=1
  · have hne : r≠c := by intro h;subst r;nlinarith [sq_abs c]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
  · have hcLt : c^2<1 := lt_of_le_of_ne hc he
    nlinarith

lemma secondDen_eq (r c : ℝ) : secondDen r c=poissonDen r c*poissonDen (-r) c := by
  unfold secondDen poissonDen
  ring

lemma secondDen_lower {r c : ℝ} (hr : |r| ≤ 1/2) (hc : c^2 ≤ 1) :
    (9:ℝ)/16 ≤ secondDen r c := by
  have hrsq : r^2 ≤ 1/4 := by nlinarith [sq_abs r,sq_nonneg (|r|+1/2),abs_nonneg r]
  unfold secondDen
  nlinarith [sq_nonneg (1-r^2),mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hc)]

lemma secondKernel_abs_le {r : ℝ} (hr : |r| ≤ 1/2) {z : ℂ} (hz : ‖z‖=1) :
    |secondKernel r z| ≤ 4 := by
  have hc := unit_re_sq_le hz
  have hd := secondDen_lower hr hc
  have hdpos : 0 < secondDen r z.re := by linarith
  have hrsq : r^2 ≤ 1/4 := by nlinarith [sq_abs r,sq_nonneg (|r|+1/2),abs_nonneg r]
  rw [secondKernel,abs_div,abs_of_pos hdpos]
  apply (div_le_iff₀ hdpos).mpr
  apply (abs_le).mpr
  constructor <;> nlinarith [sq_nonneg z.re,sq_nonneg r]

lemma re_poisson_kernel_real {z : ℂ} (hz : ‖z‖=1) {r : ℝ} (hr : |r|<1) :
    (herglotzRieszKernel 0 (r:ℂ) z).re=(1-r^2)/poissonDen r z.re := by
  have hu := unit_re_im_sq hz
  have hd := poissonDen_pos hr (unit_re_sq_le hz)
  rw [herglotzRieszKernel_def]
  simp only [sub_zero,Complex.div_re,Complex.add_re,Complex.sub_re,Complex.add_im,
    Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,add_zero,sub_zero,Complex.normSq_apply]
  have he : (z.re-r)*(z.re-r)+z.im*z.im=poissonDen r z.re := by
    unfold poissonDen
    nlinarith [hu]
  rw [he,← add_div]
  congr 1
  nlinarith [hu]

/-- Exact symmetric second Poisson difference quotient on the unit circle. -/
lemma secondKernel_poisson_identity {z : ℂ} (hz : ‖z‖=1) {r : ℝ}
    (hr : |r|<1) (hr0 : r≠0) :
    secondKernel r z=((herglotzRieszKernel 0 (r:ℂ) z).re+
      (herglotzRieszKernel 0 ((-r:ℝ):ℂ) z).re-2)/(4*r^2) := by
  rw [re_poisson_kernel_real hz hr,re_poisson_kernel_real hz (by simpa using hr)]
  have h1 := poissonDen_pos hr (unit_re_sq_le hz)
  have h2 := poissonDen_pos (by simpa using hr : |-r|<1) (unit_re_sq_le hz)
  unfold secondKernel
  rw [secondDen_eq]
  field_simp [h1.ne',h2.ne',hr0]
  unfold poissonDen
  ring

lemma boundaryLog_circleIntegrable (rho : ℂ) : CircleIntegrable (fun z => Real.log ‖z-rho‖) 0 1 :=
  circleIntegrable_log_norm_sub_const 1

lemma poisson_log_circleIntegrable (rho : ℂ) {r : ℝ} (hr : |r|<1) :
    CircleIntegrable (fun z => (herglotzRieszKernel 0 (r:ℂ) z).re*Real.log ‖z-rho‖) 0 1 := by
  have hnot : (r:ℂ) ∉ sphere (0:ℂ) |(1:ℝ)| := by
    simpa only [abs_one,mem_sphere_iff_norm,sub_zero,Complex.norm_real,Real.norm_eq_abs] using hr.ne
  have h := (boundaryLog_circleIntegrable rho).continuousOn_smul
    (Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hnot))
  convert h using 1
  funext z
  rfl

/-- The true symmetric second Poisson average, before taking its zero-radius
limit; its right side is an actual boundary logarithm value. -/
lemma secondKernel_average_identity {rho : ℂ} (hρ : ‖rho‖=1) {r : ℝ}
    (hr : |r|<1) (hr0 : r≠0) :
    Real.circleAverage (fun z => secondKernel r z*Real.log ‖z-rho‖) 0 1=
      (Real.log ‖(r:ℂ)-rho‖+Real.log ‖((-r:ℝ):ℂ)-rho‖)/(4*r^2) := by
  have hmem : rho ∈ sphere (0:ℂ) (1:ℝ) := by simpa only [mem_sphere_iff_norm,sub_zero] using hρ
  have hpos : (r:ℂ) ∈ ball (0:ℂ) (1:ℝ) := by
    simpa only [mem_ball_iff_norm,sub_zero,Complex.norm_real,Real.norm_eq_abs] using hr
  have hneg : ((-r:ℝ):ℂ) ∈ ball (0:ℂ) (1:ℝ) := by
    simpa only [mem_ball_iff_norm,sub_zero,Complex.norm_real,Real.norm_eq_abs,abs_neg] using hr
  have hp := circleAverage_re_herglotzRieszKernel_mul_log hmem hpos
  have hn := circleAverage_re_herglotzRieszKernel_mul_log hmem hneg
  have hz := circleAverage_log_norm_sub_const₁ hρ
  have he : Real.circleAverage (fun z => secondKernel r z*Real.log ‖z-rho‖) 0 1=
      Real.circleAverage (fun z => (4*r^2)⁻¹ *
        (((herglotzRieszKernel 0 (r:ℂ) z).re*Real.log ‖z-rho‖+
          (herglotzRieszKernel 0 ((-r:ℝ):ℂ) z).re*Real.log ‖z-rho‖)-
          2*Real.log ‖z-rho‖)) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have hz' : ‖z‖=1 := by simpa only [abs_one,mem_sphere_iff_norm,sub_zero] using hz
    dsimp only
    rw [secondKernel_poisson_identity hz' hr hr0]
    ring
  rw [he,show (fun z : ℂ => (4*r^2)⁻¹ *
        (((herglotzRieszKernel 0 (r:ℂ) z).re*Real.log ‖z-rho‖+
          (herglotzRieszKernel 0 ((-r:ℝ):ℂ) z).re*Real.log ‖z-rho‖)-
          2*Real.log ‖z-rho‖)) =
      (4*r^2)⁻¹ • ((fun z => (herglotzRieszKernel 0 (r:ℂ) z).re*Real.log ‖z-rho‖)+
        (fun z => (herglotzRieszKernel 0 ((-r:ℝ):ℂ) z).re*Real.log ‖z-rho‖)-
        (2:ℝ) • (fun z => Real.log ‖z-rho‖)) from rfl,
    circleAverage_smul,circleAverage_sub,circleAverage_add,circleAverage_smul]
  · change circleAverage (fun z => (herglotzRieszKernel 0 (r:ℂ) z).re*Real.log ‖z-rho‖) 0 1=Real.log ‖(r:ℂ)-rho‖ at hp
    change circleAverage (fun z => (herglotzRieszKernel 0 ((-r:ℝ):ℂ) z).re*Real.log ‖z-rho‖) 0 1=Real.log ‖((-r:ℝ):ℂ)-rho‖ at hn
    rw [hp,hn,hz]
    simp only [smul_eq_mul,mul_zero,sub_zero]
    ring
  · exact poisson_log_circleIntegrable rho hr
  · exact poisson_log_circleIntegrable rho (by simpa using hr)
  · exact (poisson_log_circleIntegrable rho hr).add (poisson_log_circleIntegrable rho (by simpa using hr))
  · exact (boundaryLog_circleIntegrable rho).const_smul

lemma secondKernel_continuousOn {r : ℝ} (hr : |r|<1) :
    ContinuousOn (secondKernel r) (sphere (0:ℂ) |(1:ℝ)|) := by
  apply ContinuousOn.div (by fun_prop) (by unfold secondDen;fun_prop)
  intro z hz
  have hu : ‖z‖=1 := by simpa only [abs_one,mem_sphere_iff_norm,sub_zero] using hz
  rw [secondDen_eq]
  exact mul_ne_zero (poissonDen_pos hr (unit_re_sq_le hu)).ne'
    (poissonDen_pos (by simpa using hr : |-r|<1) (unit_re_sq_le hu)).ne'

lemma secondKernel_log_circleIntegrable (rho : ℂ) {r : ℝ} (hr : |r|<1) :
    CircleIntegrable (fun z => secondKernel r z*Real.log ‖z-rho‖) 0 1 := by
  have h := (boundaryLog_circleIntegrable rho).continuousOn_smul (secondKernel_continuousOn hr)
  convert h using 1

def approxRadius (n : ℕ) : ℝ := 1/((n:ℝ)+3)

lemma approxRadius_pos (n : ℕ) : 0 < approxRadius n := by unfold approxRadius;positivity

lemma approxRadius_le (n : ℕ) : approxRadius n ≤ 1/3 := by
  unfold approxRadius
  apply one_div_le_one_div_of_le (by norm_num)
  have h := Nat.cast_nonneg (α := ℝ) n
  linarith

lemma approxRadius_abs_le (n : ℕ) : |approxRadius n| ≤ 1/2 := by
  rw [abs_of_pos (approxRadius_pos n)]
  linarith [approxRadius_le n]

lemma approxRadius_lt (n : ℕ) : |approxRadius n|<1 := by linarith [approxRadius_abs_le n]

lemma approxRadius_tendsto : Tendsto approxRadius atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (3:ℝ)))
  convert tendsto_inv_atTop_zero.comp ht using 1
  funext n
  simp only [approxRadius,one_div,Function.comp_def]

lemma secondKernel_continuousAt_zero (z : ℂ) : ContinuousAt (fun r => secondKernel r z) 0 := by
  apply ContinuousAt.div (by fun_prop) (by unfold secondDen;fun_prop)
  norm_num [secondDen]

/-- A genuine dominated-convergence limit extracts the second circle Fourier
coefficient from the bounded symmetric Poisson quotient. -/
lemma secondKernel_average_tendsto (rho : ℂ) :
    Tendsto (fun n => circleAverage (fun z => secondKernel (approxRadius n) z*Real.log ‖z-rho‖) 0 1)
      atTop (𝓝 (circleAverage (fun z => (2*z.re^2-1)*Real.log ‖z-rho‖) 0 1)) := by
  let bound := fun theta : ℝ => 4*|Real.log ‖circleMap 0 1 theta-rho‖|
  have hI : IntervalIntegrable (fun theta => Real.log ‖circleMap 0 1 theta-rho‖) volume 0 (2*Real.pi) :=
    boundaryLog_circleIntegrable rho
  have hlimit : Tendsto (fun n => ∫ theta in (0:ℝ)..(2*Real.pi),
      secondKernel (approxRadius n) (circleMap 0 1 theta)*Real.log ‖circleMap 0 1 theta-rho‖)
      atTop (𝓝 (∫ theta in (0:ℝ)..(2*Real.pi),
        (2*(circleMap 0 1 theta).re^2-1)*Real.log ‖circleMap 0 1 theta-rho‖)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    · apply Eventually.of_forall
      intro n
      simpa only [uIoc_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] using
        (secondKernel_log_circleIntegrable rho (approxRadius_lt n)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      exact ae_of_all _ fun theta ht => by
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_right
          (secondKernel_abs_le (approxRadius_abs_le n) (by simp : ‖circleMap 0 1 theta‖=1)) (abs_nonneg _)
    · exact hI.abs.const_mul 4
    · exact ae_of_all _ fun theta ht => by
        have h := ((secondKernel_continuousAt_zero (circleMap 0 1 theta)).tendsto.comp
          approxRadius_tendsto).mul_const (Real.log ‖circleMap 0 1 theta-rho‖)
        simpa only [secondKernel,secondDen,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,
          mul_zero,add_zero,sub_zero,one_pow,div_one,Function.comp_def] using h
  exact tendsto_const_nhds.smul hlimit

lemma normSq_real_sub_unit {rho : ℂ} (hρ : ‖rho‖=1) (r : ℝ) :
    Complex.normSq ((r:ℂ)-rho)=poissonDen r rho.re := by
  have hu := unit_re_im_sq hρ
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,zero_sub]
  unfold poissonDen
  nlinarith [hu]

lemma boundary_log_pair {rho : ℂ} (hρ : ‖rho‖=1) {r : ℝ} (hr : |r|<1) :
    Real.log ‖(r:ℂ)-rho‖+Real.log ‖((-r:ℝ):ℂ)-rho‖=
      Real.log (secondDen r rho.re)/2 := by
  rw [Complex.norm_def,Complex.norm_def,
    Real.log_sqrt (Complex.normSq_nonneg _),Real.log_sqrt (Complex.normSq_nonneg _),
    normSq_real_sub_unit hρ r,normSq_real_sub_unit hρ (-r)]
  have hp := poissonDen_pos hr (unit_re_sq_le hρ)
  have hn := poissonDen_pos (by simpa using hr : |-r|<1) (unit_re_sq_le hρ)
  rw [secondDen_eq,Real.log_mul hp.ne' hn.ne']
  ring

lemma secondKernel_average_closed {rho : ℂ} (hρ : ‖rho‖=1) {r : ℝ}
    (hr : |r|<1) (hr0 : r≠0) :
    circleAverage (fun z => secondKernel r z*Real.log ‖z-rho‖) 0 1=
      Real.log (1+r^2*(2-4*rho.re^2+r^2))/(8*r^2) := by
  rw [secondKernel_average_identity hρ hr hr0,boundary_log_pair hρ hr]
  have he : secondDen r rho.re=1+r^2*(2-4*rho.re^2+r^2) := by unfold secondDen;ring
  rw [he]
  ring

lemma quadratic_log_slope_limit (d : ℝ) :
    Tendsto (fun n => Real.log (1+approxRadius n^2*(d+approxRadius n^2))/(8*approxRadius n^2))
      atTop (𝓝 (d/8)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.log (1+t*(d+t))) d 0 := by
    have hp := (hasDerivAt_const (0:ℝ) (1:ℝ)).add
      ((hasDerivAt_id (0:ℝ)).mul ((hasDerivAt_const (0:ℝ) d).add (hasDerivAt_id (0:ℝ))))
    have hh := hp.log (by norm_num)
    convert hh using 1 <;> simp
  have hr : Tendsto (fun n => approxRadius n^2) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => sq_pos_of_pos (approxRadius_pos n)⟩
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0)] using approxRadius_tendsto.pow 2
  have hs := hd.tendsto_slope_zero_right.comp hr
  convert hs.div_const 8 using 1
  funext n
  simp only [Function.comp_def,zero_add,zero_mul,add_zero,Real.log_one,sub_zero,smul_eq_mul]
  field_simp

/-- The actual second Fourier coefficient of a boundary logarithm. It is
obtained from the genuine Poisson representation and a proved dominated
convergence limit, rather than postulated as a Fourier expansion. -/
theorem second_boundary_log_moment {rho : ℂ} (hρ : ‖rho‖=1) :
    circleAverage (fun z => (2*z.re^2-1)*Real.log ‖z-rho‖) 0 1=-(2*rho.re^2-1)/4 := by
  have hlim := quadratic_log_slope_limit (2-4*rho.re^2)
  have hAvg : Tendsto (fun n => circleAverage (fun z => secondKernel (approxRadius n) z*Real.log ‖z-rho‖) 0 1)
      atTop (𝓝 ((2-4*rho.re^2)/8)) := by
    apply hlim.congr
    intro n
    exact (secondKernel_average_closed hρ (approxRadius_lt n) (approxRadius_pos n).ne').symm
  have he := tendsto_nhds_unique (secondKernel_average_tendsto rho) hAvg
  exact he.trans (by ring)

/-- The exact quadratic angular weight of the semicircle evaluates a unit
boundary logarithm to one quarter of its second cosine coefficient. -/
theorem semicircle_weight_boundary_log_moment {rho : ℂ} (hρ : ‖rho‖=1) :
    circleAverage (fun z => (1-(2*z.re^2-1))*Real.log ‖z-rho‖) 0 1=(2*rho.re^2-1)/4 := by
  have he : (fun z : ℂ => (1-(2*z.re^2-1))*Real.log ‖z-rho‖)=
      (fun z => Real.log ‖z-rho‖)-(fun z => (2*z.re^2-1)*Real.log ‖z-rho‖) := by
    funext z
    change (1-(2*z.re^2-1))*Real.log ‖z-rho‖ = Real.log ‖z-rho‖-(2*z.re^2-1)*Real.log ‖z-rho‖
    ring
  have hK : CircleIntegrable (fun z => (2*z.re^2-1)*Real.log ‖z-rho‖) 0 1 := by
    have h := (boundaryLog_circleIntegrable rho).continuousOn_smul
      (show ContinuousOn (fun z : ℂ => 2*z.re^2-1) (sphere (0:ℂ) |(1:ℝ)|) from by fun_prop)
    convert h using 1
  rw [he,circleAverage_sub (boundaryLog_circleIntegrable rho) hK,
    circleAverage_log_norm_sub_const₁ hρ,second_boundary_log_moment hρ]
  ring

end
end SlowEquilibration.CircleLogMoment
