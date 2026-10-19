-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedVarianceSecond
public import SlowEquilibration.SphericalTAPMixedMeanContactSecond

@[expose] public section

/-! The actual latitude curvature of the literal mixed Laplace exponent. -/

namespace SlowEquilibration.SphericalTAPMixedActualLatitudeHessian
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPMixedBandExponent SphericalTAPMixedMeanContactSecond
open SphericalTAPMixedVarianceSecond
open scoped Topology
set_option autoImplicit false

private theorem log_latitude_first (a : ℝ) (ha : |a| < 1) :
    deriv (fun t : ℝ => Real.log (1-t^2)/2) a = -a/(1-a^2) := by
  have hp : 0 < 1-a^2 := by nlinarith [(abs_lt.mp ha).1,(abs_lt.mp ha).2]
  have hd : HasDerivAt (fun t : ℝ => 1-t^2) (-2*a) a := by
    convert (hasDerivAt_const a 1).sub ((hasDerivAt_id a).pow 2) using 1
    · funext t
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hh := (hd.log hp.ne').div_const 2
  convert hh.deriv using 1
  ring

private theorem log_latitude_second {Q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (fun t : ℝ => Real.log (1-t^2)/2)) (Real.sqrt Q) =
      -(1+Q)/(1-Q)^2 := by
  let q := Real.sqrt Q
  have hq0 : 0 < q := Real.sqrt_pos.mpr hQ.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hQ.1.le hQ.2
  have he : deriv (fun t : ℝ => Real.log (1-t^2)/2) =ᶠ[𝓝 q]
      fun t => -t/(1-t^2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show q ∈ Ioo (-1 : ℝ) 1 by
      constructor <;> linarith)] with a ha
    exact log_latitude_first a (abs_lt.mpr ha)
  rw [he.deriv_eq]
  have hden : 1-q^2 ≠ 0 := by
    rw [Real.sq_sqrt hQ.1.le]
    exact ne_of_gt (sub_pos.mpr hQ.2)
  have hd : HasDerivAt (fun t : ℝ => 1-t^2) (-2*q) q := by
    convert (hasDerivAt_const q 1).sub ((hasDerivAt_id q).pow 2) using 1
    · funext t
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hh := ((hasDerivAt_id q).neg).div hd hden
  change HasDerivAt (fun t => -t/(1-t^2)) _ q at hh
  rw [hh.deriv]
  simp only [Pi.neg_apply, id_eq]
  ring_nf
  rw [Real.sq_sqrt hQ.1.le]
  rw [show q^4=Q^2 by
    calc q^4=(q^2)^2 := by ring
      _=Q^2 := by rw [Real.sq_sqrt hQ.1.le]]

private theorem latitude_second_decompose (μ : FiniteMixture) (β Q e k a : ℝ)
    (ha : |a| < 1) :
    deriv (deriv (sourceMixedBandExponent μ β Q e k)) a =
      β*deriv (deriv (sourceMixedMean μ Q e k)) a+
        β^2/2*deriv (deriv (sourceMixedVariance μ Q)) a+
        deriv (deriv (fun t : ℝ => Real.log (1-t^2)/2)) a := by
  have hm : ContDiffAt ℝ 2 (sourceMixedMean μ Q e k) a :=
    (SphericalTAPMixedLatitudeSmooth.sourceMixedMean_smooth μ Q e k).contDiffAt.of_le
      (by norm_num)
  have hv : ContDiffAt ℝ 2 (sourceMixedVariance μ Q) a :=
    (SphericalTAPMixedLatitudeSmooth.sourceMixedVariance_smooth μ Q).contDiffAt.of_le
      (by norm_num)
  have hl : ContDiffAt ℝ 2 (fun t : ℝ => Real.log (1-t^2)/2) a := by
    have hden : 1-a^2 ≠ 0 := ne_of_gt (by
      nlinarith [(abs_lt.mp ha).1,(abs_lt.mp ha).2])
    fun_prop
  have hiter (f : ℝ → ℝ) : iteratedDeriv 2 f a = deriv (deriv f) a := by
    simp [iteratedDeriv_eq_iterate, Function.iterate_succ_apply]
  rw [← hiter (sourceMixedBandExponent μ β Q e k)]
  have hfun : sourceMixedBandExponent μ β Q e k = fun t =>
      sourceRadialProfile μ Q e k+
        (β*sourceMixedMean μ Q e k t+β^2/2*sourceMixedVariance μ Q t)+
        Real.log (1-t^2)/2 := rfl
  rw [hfun]
  have hβm : ContDiffAt ℝ 2
      (fun t => β*sourceMixedMean μ Q e k t) a := contDiffAt_const.mul hm
  have hβv : ContDiffAt ℝ 2
      (fun t => β^2/2*sourceMixedVariance μ Q t) a := contDiffAt_const.mul hv
  have hmid : ContDiffAt ℝ 2
      (fun t => β*sourceMixedMean μ Q e k t+
        β^2/2*sourceMixedVariance μ Q t) a := hβm.add hβv
  have houter : ContDiffAt ℝ 2
      (fun t => sourceRadialProfile μ Q e k+
        (β*sourceMixedMean μ Q e k t+β^2/2*sourceMixedVariance μ Q t)) a :=
    contDiffAt_const.add hmid
  rw [← hiter (sourceMixedMean μ Q e k),
    ← hiter (sourceMixedVariance μ Q),
    ← hiter (fun t : ℝ => Real.log (1-t^2)/2)]
  have hsplit : (fun t => sourceRadialProfile μ Q e k+
      (β*sourceMixedMean μ Q e k t+β^2/2*sourceMixedVariance μ Q t)+
      Real.log (1-t^2)/2) =
      (fun t => sourceRadialProfile μ Q e k+
        (β*sourceMixedMean μ Q e k t+β^2/2*sourceMixedVariance μ Q t))+
      (fun t => Real.log (1-t^2)/2) := rfl
  rw [hsplit]
  rw [iteratedDeriv_add houter hl]
  rw [iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ))]
  have hsplit2 : (fun t => β*sourceMixedMean μ Q e k t+
      β^2/2*sourceMixedVariance μ Q t) =
      (fun t => β*sourceMixedMean μ Q e k t)+
      (fun t => β^2/2*sourceMixedVariance μ Q t) := rfl
  rw [hsplit2]
  rw [iteratedDeriv_add hβm hβv]
  simp only [iteratedDeriv_const_mul_field]

/-- The literal joint exponent's contact latitude curvature, before the
stationarity simplification. This exposes the cancellation of ξ'''(Q). -/
theorem sourceMixedBandExponent_latitude_second_contact_raw
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    deriv (deriv (sourceMixedBandExponent μ β Q
      (markE μ β x Q) (markK μ β Q))) (Real.sqrt Q) =
      β*((2*Q*μ.xi2 Q+Q^2*μ.v1 Q)+
          markZ x Q*(Q*μ.xi2 Q))/markY β Q+
        β^2/2*(4*Q*μ.xi2 Q-
          2*(1-Q)*Q*((μ.xi2 Q)^2/μ.xi1 Q+μ.v1 Q))-
        (1+Q)/(1-Q)^2 := by
  have hq0 : 0 < Real.sqrt Q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : Real.sqrt Q < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  rw [latitude_second_decompose μ β Q (markE μ β x Q) (markK μ β Q)
    (Real.sqrt Q) (abs_lt.mpr (by constructor <;> linarith)),
    sourceMixedMean_second_contact_marks μ h hnp,
    sourceMixedVariance_second_contact μ h.overlap_range.1 hnp,
    log_latitude_second h.overlap_range]
  ring

/-- The printed mixed latitude Hessian entry of Lemma 12.15 is the second
derivative of the actual exponent `g`, at the certified source saddle. -/
theorem sourceMixedBandExponent_latitude_second_contact
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    deriv (deriv (sourceMixedBandExponent μ β Q
      (markE μ β x Q) (markK μ β Q))) (Real.sqrt Q) =
      -(1-markB μ Q/(markY β Q)^2)*
        (1+Q-profileConstant x Q*(markB μ Q/(markY β Q)^2))/(1-Q)^2 := by
  rw [sourceMixedBandExponent_latitude_second_contact_raw μ h hnp]
  let s := 1-Q
  let C := profileConstant x Q
  have hβ0 : β ≠ 0 := h.beta_pos.ne'
  have hQ0 : Q ≠ 0 := h.overlap_range.1.ne'
  have hs0 : s ≠ 0 := ne_of_gt (sub_pos.mpr h.overlap_range.2)
  have hC0 : C ≠ 0 :=
    (profileConstant_pos h.weight_range h.overlap_range).ne'
  have hxi : μ.xi1 Q = Q/(β^2*s*C) := by
    have hst := h.contact_equations.1
    dsimp [s,C] at *
    apply (eq_div_iff (by positivity : β^2*(1-Q)*profileConstant x Q ≠ 0)).mpr
    field_simp at hst ⊢
    nlinarith [hst]
  rw [hxi]
  unfold markY markZ markB
  change
    β*((2*Q*μ.xi2 Q+Q^2*μ.v1 Q)+
        (x*Q/s)*(Q*μ.xi2 Q))/(Q/(β*s))+
      β^2/2*(4*Q*μ.xi2 Q-
        2*s*Q*((μ.xi2 Q)^2/(Q/(β^2*s*C))+μ.v1 Q))-
      (1+Q)/s^2 =
      -(1-(Q^2*μ.xi2 Q)/(Q/(β*s))^2)*
        (1+Q-C*((Q^2*μ.xi2 Q)/(Q/(β*s))^2))/s^2
  field_simp [hβ0,hQ0,hs0,hC0]
  dsimp [s,C,profileConstant]
  ring

end
end SlowEquilibration.SphericalTAPMixedActualLatitudeHessian
