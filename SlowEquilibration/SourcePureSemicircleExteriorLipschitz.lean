-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemicirclePotential
public import SlowEquilibration.GOEPhysicalClippedResolventL2
public import SlowEquilibration.SourcePureOnePointSignedSlope
public import Mathlib.Analysis.Calculus.MeanValue

/-! A quantitative local regularity bound for the actual semicircle
resolvent on the exterior score interval used by the proper-pure source
contact. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SemicirclePotential
open Set MeasureTheory GOEClippedResolvent GOELogPotential
set_option maxHeartbeats 400000

private theorem resolventSquare_nonneg {z : ℝ} (_hz : 2 < z) :
    0 ≤ resolventSquare z := by
  unfold resolventSquare
  apply intervalIntegral.integral_nonneg (by norm_num : (-2 : ℝ) ≤ 2)
  intro t ht
  exact div_nonneg (density_nonneg _) (sq_nonneg _)

/-- The true semicircle inverse-square trace has its elementary spectral-gap
bound, derived from the literal semicircle-density integral. -/
theorem resolventSquare_le_inv_gap_sq {z : ℝ} (hz : 2 < z) :
    resolventSquare z ≤ 1/(z-2)^2 := by
  have hi : IntervalIntegrable (fun t => density t/(z-t)^2) volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr
      (resolventSquare_integrable hz)
  have hConst : IntervalIntegrable (fun t => density t/(z-2)^2) volume (-2 : ℝ) 2 :=
    density_continuous.intervalIntegrable (-2 : ℝ) 2 |>.div_const _
  unfold resolventSquare
  calc
    _ ≤ ∫ t in (-2 : ℝ)..2, density t/(z-2)^2 := by
      apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2) hi hConst
      intro t ht
      have hGap : 0 < z-t := by linarith [ht.2]
      have hDen : (z-2)^2 ≤ (z-t)^2 :=
        pow_le_pow_left₀ (sub_pos.mpr hz).le (by linarith [ht.2]) 2
      exact div_le_div_of_nonneg_left (density_nonneg _) (sq_pos_of_pos (sub_pos.mpr hz)) hDen
    _ = 1/(z-2)^2 := by rw [intervalIntegral.integral_div,density_integral_interval]

/-- Uniform Lipschitz continuity of the literal semicircle resolvent outside
a fixed spectral gap. -/
theorem resolvent_lipschitz_above_gap {g : ℝ} (hg : 0 < g)
    {u v : ℝ} (hu : 2+g ≤ u) (hv : 2+g ≤ v) :
    |resolvent v-resolvent u| ≤ |v-u|/g^2 := by
  let s : Set ℝ := Ici (2+g)
  have hDiff : ∀ z ∈ s, DifferentiableAt ℝ resolvent z := by
    intro z hz
    exact (resolvent_hasDerivAt (by have hh : 2+g ≤ z := hz; linarith)).differentiableAt
  have hBound : ∀ z ∈ s, ‖deriv resolvent z‖ ≤ 1/g^2 := by
    intro z hz
    have hzg : g ≤ z-2 := by have hh : 2+g ≤ z := hz; linarith
    have hz2 : 2 < z := by linarith
    rw [(resolvent_hasDerivAt hz2).deriv,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg (resolventSquare_nonneg hz2)]
    calc
      resolventSquare z ≤ 1/(z-2)^2 := resolventSquare_le_inv_gap_sq hz2
      _ ≤ 1/g^2 := by
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
          (sq_pos_of_pos hg)
        exact pow_le_pow_left₀ hg.le hzg 2
  have hh := (convex_Ici (2+g)).norm_image_sub_le_of_norm_deriv_le hDiff hBound hu hv
  simpa only [Real.norm_eq_abs,one_div,div_eq_mul_inv,mul_comm,mul_one] using hh

end SlowEquilibration.SemicirclePotential

namespace SlowEquilibration.GOEClippedResolvent
open SlowEquilibration.SemicirclePotential

/-- In physical GOE units the variance scale cancels: the limiting
resolvent's Lipschitz constant above a physical gap `g` is `g⁻²`. -/
theorem physicalResolvent_lipschitz_above_gap {b g : ℝ} (hb : 0 < b) (hg : 0 < g)
    {u v : ℝ} (hu : 2*Real.sqrt b+g ≤ u) (hv : 2*Real.sqrt b+g ≤ v) :
    |physicalResolvent b v-physicalResolvent b u| ≤ |v-u|/g^2 := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hgs : 0 < g/Real.sqrt b := div_pos hg hs
  have hgu : 2+g/Real.sqrt b ≤ u/Real.sqrt b := by
    have hh := div_le_div_of_nonneg_right hu hs.le
    convert hh using 1; field_simp [hs.ne']
  have hgv : 2+g/Real.sqrt b ≤ v/Real.sqrt b := by
    have hh := div_le_div_of_nonneg_right hv hs.le
    convert hh using 1; field_simp [hs.ne']
  have huEdge : 2 < u/Real.sqrt b := by linarith
  have hvEdge : 2 < v/Real.sqrt b := by linarith
  have hRu : physicalResolvent b u =
      (Real.sqrt b)⁻¹*SemicirclePotential.resolvent (u/Real.sqrt b) := by
    unfold physicalResolvent
    rw [SemicirclePotential.resolvent_eq_semicircleResolvent huEdge]
  have hRv : physicalResolvent b v =
      (Real.sqrt b)⁻¹*SemicirclePotential.resolvent (v/Real.sqrt b) := by
    unfold physicalResolvent
    rw [SemicirclePotential.resolvent_eq_semicircleResolvent hvEdge]
  have hRes := SemicirclePotential.resolvent_lipschitz_above_gap hgs hgu hgv
  rw [hRu,hRv,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hs)]
  calc
    (Real.sqrt b)⁻¹ * |SemicirclePotential.resolvent (v/Real.sqrt b)-SemicirclePotential.resolvent (u/Real.sqrt b)| ≤
      (Real.sqrt b)⁻¹ * (|v/Real.sqrt b-u/Real.sqrt b|/(g/Real.sqrt b)^2) :=
        mul_le_mul_of_nonneg_left hRes (inv_pos.mpr hs).le
    _ = |v-u|/g^2 := by
      rw [←sub_div,abs_div,abs_of_pos hs]
      have hsq := Real.sq_sqrt hb.le
      field_simp [hs.ne', hg.ne']

end SlowEquilibration.GOEClippedResolvent

namespace SlowEquilibration.SphericalMarkedWindows
open GOEClippedResolvent Filter TwoAtomStationarity SphericalTAPCertificate
open scoped Topology

/-- Quantitative one-point signed slope control at an exterior contact.
This separates the genuine finite GOE error from the displacement of the
limiting semicircle score. -/
theorem pureSignedEnergyLogWeight_contact_slope_bound
    (n : ℕ) {V b p E βx g σ : ℝ}
    (hV : 0 < V) (hb : 0 < b) (hp : 0 ≤ p) (hg : 0 < g)
    (hContactGap : 2*Real.sqrt b+g ≤ p*E)
    (hShiftGap : 2*Real.sqrt b+g ≤ p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))
    (hContactScore : -E/V+p*physicalResolvent b (p*E)=-βx) :
    |deriv (pureSignedEnergyLogWeight n V b p) ((n+2 : ℕ)*E+σ)+βx| ≤
      ((p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g))/(n+1 : ℕ)+
        (1/V+p^2/g^2)*|σ|/(n+2 : ℕ) := by
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hRate := pureSignedEnergyLogWeight_slope_rate n hV hb hp hg hShiftGap
  have hRes := physicalResolvent_lipschitz_above_gap hb hg hContactGap hShiftGap
  have hK : p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ) = p*E+p*σ/(n+2 : ℕ) := by
    field_simp
  have hKabs : |p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ)-p*E|=p*|σ|/(n+2 : ℕ) := by
    rw [hK]
    have hh : p*E+p*σ/(n+2 : ℕ)-p*E=p*σ/(n+2 : ℕ) := by ring
    rw [hh,abs_div,abs_mul,abs_of_nonneg hp,abs_of_pos hN]
  rw [hKabs] at hRes
  have hScore :
      |(-((n+2 : ℕ)*E+σ)/((n+2 : ℕ)*V)+
          p*physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ)))-
        (-E/V+p*physicalResolvent b (p*E))| ≤
        (1/V+p^2/g^2)*|σ|/(n+2 : ℕ) := by
    have hEq :
        (-((n+2 : ℕ)*E+σ)/((n+2 : ℕ)*V)+
          p*physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ)))-
        (-E/V+p*physicalResolvent b (p*E)) =
        -σ/((n+2 : ℕ)*V)+
          p*(physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))-
            physicalResolvent b (p*E)) := by
      field_simp
      ring
    rw [hEq]
    calc
      _ ≤ |-σ/((n+2 : ℕ)*V)|+
          |p*(physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))-
            physicalResolvent b (p*E))| := abs_add_le _ _
      _ = |σ|/((n+2 : ℕ)*V)+
          p*|physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))-
            physicalResolvent b (p*E)| := by
        simp only [abs_div,abs_neg,abs_mul,abs_of_nonneg hp,
          abs_of_pos hN,abs_of_pos hV]
      _ ≤ |σ|/((n+2 : ℕ)*V)+p*((p*|σ|/(n+2 : ℕ))/g^2) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hRes hp) _
      _ = (1/V+p^2/g^2)*|σ|/(n+2 : ℕ) := by
        field_simp
  rw [hContactScore] at hScore
  have hScore' :
      |(-((n+2 : ℕ)*E+σ)/((n+2 : ℕ)*V)+
          p*physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ)))+βx| ≤
        (1/V+p^2/g^2)*|σ|/(n+2 : ℕ) := by
    simpa only [sub_neg_eq_add] using hScore
  have hh := (abs_add_le
    (deriv (pureSignedEnergyLogWeight n V b p) ((n+2 : ℕ)*E+σ)-
      (-((n+2 : ℕ)*E+σ)/((n+2 : ℕ)*V)+
        p*physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))))
    ((-((n+2 : ℕ)*E+σ)/((n+2 : ℕ)*V)+
        p*physicalResolvent b (p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ)))+βx))
  convert (hh.trans (add_le_add hRate hScore')) using 1; ring

/-- The signed one-point log-weight is quadratically close to its contact
tangent over every positive displacement that remains in the exterior
regime. This is the finite-dimensional estimate needed at logarithmic
source centerings. -/
theorem pureSignedEnergyLogWeight_contact_positive_shift_bound
    (n : ℕ) {V b p E βx g σ : ℝ}
    (hV : 0 < V) (hb : 0 < b) (hp : 0 ≤ p) (hg : 0 < g)
    (hContactGap : 2*Real.sqrt b+g ≤ p*E)
    (hContactScore : -E/V+p*physicalResolvent b (p*E)=-βx)
    (hσ : 0 ≤ σ) :
    |pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E+σ)-
      pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E)+βx*σ| ≤
      σ*(((p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g))/(n+1 : ℕ)+
        (1/V+p^2/g^2)*σ/(n+2 : ℕ)) := by
  rcases eq_or_lt_of_le hσ with hZero | hPos
  · subst σ
    simp
  let N : ℝ := (n+2 : ℕ)
  let f := pureSignedEnergyLogWeight n V b p
  let A := 1/V+p^2/g^2
  let K := ((p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g))/(n+1 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hArg (H : ℝ) (hH : N*E ≤ H) :
      2*Real.sqrt b+g ≤ p*H/N := by
    have hm := mul_le_mul_of_nonneg_left hH hp
    have hd := div_le_div_of_nonneg_right hm hN.le
    have heq : p*(N*E)/N=p*E := by field_simp
    rw [heq] at hd
    exact hContactGap.trans hd
  have hCont : ContinuousOn f (Set.Icc (N*E) (N*E+σ)) := by
    intro H hH
    have hh := hArg H hH.1
    have hEdge : 2*Real.sqrt b < p*H/N := by linarith
    exact (pureSignedEnergyLogWeight_hasDerivAt n hV hb hEdge).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ f (Set.Ioo (N*E) (N*E+σ)) := by
    intro H hH
    have hh := hArg H hH.1.le
    have hEdge : 2*Real.sqrt b < p*H/N := by linarith
    exact (pureSignedEnergyLogWeight_hasDerivAt n hV hb hEdge).differentiableAt.differentiableWithinAt
  obtain ⟨c,hc,hSlope⟩ := exists_deriv_eq_slope f
    (by linarith : N*E < N*E+σ) hCont hDiff
  have hcLower : 0 ≤ c-N*E := by linarith [hc.1]
  have hcUpper : c-N*E ≤ σ := by linarith [hc.2]
  have hAtC : 2*Real.sqrt b+g ≤ p*c/N := hArg c hc.1.le
  have hBound := pureSignedEnergyLogWeight_contact_slope_bound n hV hb hp hg
    hContactGap (show 2*Real.sqrt b+g ≤ p*(N*E+(c-N*E))/N by
      convert hAtC using 1; ring) hContactScore
  have hDeriv : |deriv f c+βx| ≤ K+A*σ/N := by
    have hAmon : A*(c-N*E)/N ≤ A*σ/N := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcUpper hA) hN.le
    have hcExpr : N*E+(c-N*E)=c := by ring
    dsimp [N,f,A,K] at hBound ⊢
    dsimp [N,A] at hAmon
    rw [hcExpr,abs_of_nonneg hcLower] at hBound
    exact hBound.trans (add_le_add_right hAmon _)
  have hDen : (N*E+σ)-N*E=σ := by ring
  rw [hDen] at hSlope
  have hMul := (eq_div_iff hPos.ne').mp hSlope
  have hEq : f (N*E+σ)-f (N*E)+βx*σ=σ*(deriv f c+βx) := by
    nlinarith [hMul]
  change |f (N*E+σ)-f (N*E)+βx*σ| ≤ σ*(K+A*σ/N)
  rw [hEq,abs_mul,abs_of_pos hPos]
  exact mul_le_mul_of_nonneg_left hDeriv hPos.le

/-- The same quadratic contact-tangent estimate on the lower-energy side,
provided the shifted endpoint stays outside the GOE spectral edge. -/
theorem pureSignedEnergyLogWeight_contact_negative_shift_bound
    (n : ℕ) {V b p E βx g σ : ℝ}
    (hV : 0 < V) (hb : 0 < b) (hp : 0 ≤ p) (hg : 0 < g)
    (hContactGap : 2*Real.sqrt b+g ≤ p*E)
    (hShiftGap : 2*Real.sqrt b+g ≤ p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))
    (hContactScore : -E/V+p*physicalResolvent b (p*E)=-βx)
    (hσ : σ ≤ 0) :
    |pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E+σ)-
      pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E)+βx*σ| ≤
      |σ| * (((p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g))/(n+1 : ℕ)+
        (1/V+p^2/g^2)*|σ|/(n+2 : ℕ)) := by
  rcases eq_or_lt_of_le hσ with hZero | hNeg
  · subst σ
    simp
  let N : ℝ := (n+2 : ℕ)
  let f := pureSignedEnergyLogWeight n V b p
  let A := 1/V+p^2/g^2
  let K := ((p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g))/(n+1 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hArg (H : ℝ) (hH : N*E+σ ≤ H) :
      2*Real.sqrt b+g ≤ p*H/N := by
    have hm := mul_le_mul_of_nonneg_left hH hp
    have hd := div_le_div_of_nonneg_right hm hN.le
    exact hShiftGap.trans hd
  have hCont : ContinuousOn f (Set.Icc (N*E+σ) (N*E)) := by
    intro H hH
    have hh := hArg H hH.1
    have hEdge : 2*Real.sqrt b < p*H/N := by linarith
    exact (pureSignedEnergyLogWeight_hasDerivAt n hV hb hEdge).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ f (Set.Ioo (N*E+σ) (N*E)) := by
    intro H hH
    have hh := hArg H hH.1.le
    have hEdge : 2*Real.sqrt b < p*H/N := by linarith
    exact (pureSignedEnergyLogWeight_hasDerivAt n hV hb hEdge).differentiableAt.differentiableWithinAt
  obtain ⟨c,hc,hSlope⟩ := exists_deriv_eq_slope f
    (by linarith : N*E+σ < N*E) hCont hDiff
  have hcLower : σ ≤ c-N*E := by linarith [hc.1]
  have hcUpper : c-N*E ≤ 0 := by linarith [hc.2]
  have hAtC : 2*Real.sqrt b+g ≤ p*c/N := hArg c hc.1.le
  have hBound := pureSignedEnergyLogWeight_contact_slope_bound n hV hb hp hg
    hContactGap (show 2*Real.sqrt b+g ≤ p*(N*E+(c-N*E))/N by
      convert hAtC using 1; ring) hContactScore
  have hDeriv : |deriv f c+βx| ≤ K+A*|σ|/N := by
    have hAbs : |c-N*E| ≤ |σ| := by
      rw [abs_of_nonpos hcUpper,abs_of_nonpos hσ]
      linarith
    have hAmon : A*|c-N*E|/N ≤ A*|σ|/N := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAbs hA) hN.le
    have hcExpr : N*E+(c-N*E)=c := by ring
    dsimp [N,f,A,K] at hBound ⊢
    dsimp [N,A] at hAmon
    rw [hcExpr] at hBound
    exact hBound.trans (add_le_add_right hAmon _)
  have hDen : N*E-(N*E+σ)=-σ := by ring
  rw [hDen] at hSlope
  have hMul := (eq_div_iff (by linarith : -σ ≠ 0)).mp hSlope
  have hEq : f (N*E+σ)-f (N*E)+βx*σ=σ*(deriv f c+βx) := by
    nlinarith [hMul]
  change |f (N*E+σ)-f (N*E)+βx*σ| ≤ |σ| * (K+A*|σ|/N)
  rw [hEq,abs_mul]
  exact mul_le_mul_of_nonneg_left hDeriv (abs_nonneg σ)

/-- Uniform contact-tangent estimate on either side of the source contact,
with the two endpoints separated from the spectral edge. -/
theorem pureSignedEnergyLogWeight_contact_shift_bound
    (n : ℕ) {V b p E βx g σ : ℝ}
    (hV : 0 < V) (hb : 0 < b) (hp : 0 ≤ p) (hg : 0 < g)
    (hContactGap : 2*Real.sqrt b+g ≤ p*E)
    (hShiftGap : 2*Real.sqrt b+g ≤ p*((n+2 : ℕ)*E+σ)/(n+2 : ℕ))
    (hContactScore : -E/V+p*physicalResolvent b (p*E)=-βx) :
    |pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E+σ)-
      pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E)+βx*σ| ≤
      |σ| * (((p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g))/(n+1 : ℕ)+
        (1/V+p^2/g^2)*|σ|/(n+2 : ℕ)) := by
  rcases lt_or_ge σ 0 with hσ | hσ
  · exact pureSignedEnergyLogWeight_contact_negative_shift_bound n hV hb hp hg
      hContactGap hShiftGap hContactScore hσ.le
  · simpa only [abs_of_nonneg hσ] using
      pureSignedEnergyLogWeight_contact_positive_shift_bound n hV hb hp hg
        hContactGap hContactScore hσ

/-- The quadratic error vanishes uniformly along any logarithmically
bounded source-energy displacement whose GOE arguments remain exterior. -/
theorem pureSignedEnergyLogWeight_contact_log_window_tangent
    {V b p E βx g D : ℝ}
    (hV : 0 < V) (hb : 0 < b) (hp : 0 ≤ p) (hg : 0 < g)
    (hContactGap : 2*Real.sqrt b+g ≤ p*E)
    (hContactScore : -E/V+p*physicalResolvent b (p*E)=-βx)
    (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in Filter.atTop, |σ n| ≤ D*Real.log (n+2 : ℕ))
    (hShiftGap : ∀ᶠ n : ℕ in Filter.atTop,
      2*Real.sqrt b+g ≤ p*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)) :
    Filter.Tendsto (fun n : ℕ =>
      pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E+σ n)-
        pureSignedEnergyLogWeight n V b p ((n+2 : ℕ)*E)+βx*σ n)
      Filter.atTop (nhds 0) := by
  have hAbsDiv : Tendsto (fun n : ℕ => |σ n|/(n+1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    have hUpper : Tendsto (fun n : ℕ => 2*D*Real.log (n+2 : ℕ)/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [pow_one,mul_div_assoc,mul_zero] using
        (NatLogWindowScales.log_power_div_dimension_tendsto_zero 1).const_mul (2*D)
    apply squeeze_zero_norm' _ hUpper
    filter_upwards [hσ] with n hn
    have hN1 : 0 < ((n+1 : ℕ) : ℝ) := by positivity
    have hN2 : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hInv : 1/((n+1 : ℕ) : ℝ) ≤ 2/(n+2 : ℕ) := by
      apply (div_le_div_iff₀ hN1 hN2).mpr
      push_cast
      nlinarith
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (abs_nonneg _),abs_of_pos hN1]
    calc
      |σ n|/(n+1 : ℕ) = |σ n| * (1/(n+1 : ℕ)) := by ring
      _ ≤ |σ n| * (2/(n+2 : ℕ)) := mul_le_mul_of_nonneg_left hInv (abs_nonneg _)
      _ ≤ D*Real.log (n+2 : ℕ)*(2/(n+2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hn (div_nonneg (by norm_num) hN2.le)
      _ = 2*D*Real.log (n+2 : ℕ)/(n+2 : ℕ) := by ring
  have hSqDiv : Tendsto (fun n : ℕ => (σ n)^2/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    have hUpper : Tendsto (fun n : ℕ => D^2*(Real.log (n+2 : ℕ))^2/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_div_assoc,mul_zero] using
        (NatLogWindowScales.log_power_div_dimension_tendsto_zero 2).const_mul (D^2)
    apply squeeze_zero_norm' _ hUpper
    filter_upwards [hσ] with n hn
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hLog : 0 ≤ Real.log (n+2 : ℕ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n+2 by omega))
    have hSq := (sq_le_sq₀ (abs_nonneg (σ n)) (mul_nonneg hD hLog)).mpr hn
    rw [sq_abs,mul_pow] at hSq
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg _),abs_of_pos hN]
    exact div_le_div_of_nonneg_right hSq hN.le
  let C := (p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g)
  let A := 1/V+p^2/g^2
  have hErr : Tendsto (fun n : ℕ =>
      |σ n| * (C/(n+1 : ℕ)+A*|σ n|/(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
    have h1 := hAbsDiv.const_mul C
    have h2 := hSqDiv.const_mul A
    convert h1.add h2 using 1
    · funext n
      rw [←sq_abs (σ n)]
      ring
    · ring
  apply squeeze_zero_norm' _ hErr
  filter_upwards [hShiftGap] with n hn
  simpa only [Real.norm_eq_abs,C,A] using
    pureSignedEnergyLogWeight_contact_shift_bound n hV hb hp hg
      hContactGap hn hContactScore

/-- At the literal proper-pure source contact, the genuine signed
finite-GOE one-point energy weight has the contact exponential throughout
any logarithmically bounded centering sequence. -/
theorem sourcePure_signedEnergyLogWeight_log_window_tangent
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Tendsto (fun n : ℕ =>
      pureSignedEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n)-
        pureSignedEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E)+β*x*σ n)
      atTop (𝓝 0) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  let g := ((p : ℝ)*E-2*Real.sqrt b)/2
  have hV : 0 < V := μ.xi_pos h.overlap_range.1
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hpPos : 0 ≤ (p : ℝ) := by positivity
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hg : 0 < g := by dsimp [g]; linarith
  have hContactGap : 2*Real.sqrt b+g ≤ (p : ℝ)*E := by dsimp [g]; linarith
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hE : Tendsto (fun n : ℕ => E+σ n/(n+2 : ℕ)) atTop (𝓝 E) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := E)).add hσzero
  have hk : Tendsto (fun n : ℕ => (p : ℝ)*(E+σ n/(n+2 : ℕ)))
      atTop (𝓝 ((p : ℝ)*E)) := by
    simpa using hE.const_mul (p : ℝ)
  have hShiftGap : ∀ᶠ n : ℕ in atTop,
      2*Real.sqrt b+g ≤ (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ) := by
    have hs : 2*Real.sqrt b+g < (p : ℝ)*E := by dsimp [g]; linarith
    filter_upwards [hk.eventually (Ioi_mem_nhds hs)] with n hn
    have heq : (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)=
        (p : ℝ)*(E+σ n/(n+2 : ℕ)) := by
      field_simp
    rw [heq]
    exact hn.le
  have hScore := sourcePure_signedEnergy_contact_score p hp a ha h
  change -E/V+(p : ℝ)*physicalResolvent b ((p : ℝ)*E)=-(β*x) at hScore
  exact pureSignedEnergyLogWeight_contact_log_window_tangent hV hb hpPos hg
    hContactGap hScore hD σ hσ hShiftGap

end SlowEquilibration.SphericalMarkedWindows
