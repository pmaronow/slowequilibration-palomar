-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedBandExponent
public import SlowEquilibration.SphericalOnePointContactSaddle

@[expose] public section

/-! The exterior semicircle second derivative at the mixed source contact,
and a streamlined Schur-complement argument for the printed joint Hessian.
The remaining task is to identify the literal `sourceMixedBandExponent`
second derivatives with the printed entries. -/

namespace SlowEquilibration.SphericalTAPMixedContactHessian
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open PairConditionalDeterminantMoments
set_option autoImplicit false

/-- The semicircle resolvent square at a geometric exterior point. -/
theorem resolventSquare_geometric {r : ℝ} (hr : 1 < r) :
    SemicirclePotential.resolventSquare (r+1/r)=1/(r^2-1) := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hrden : r^2-1 ≠ 0 := ne_of_gt (by nlinarith)
  have hz : 2 < r+1/r := by
    have hsq : 0 < (r-1)^2/r := div_pos (sq_pos_of_pos (by linarith)) (by linarith)
    have he : (r-1)^2/r=r+1/r-2 := by field_simp; ring
    linarith
  have hode := SemicirclePotential.resolvent_integration_by_parts hz
  rw [source_semicircle_geometric_resolvent hr] at hode
  have htest :
      (4-(r+1/r)^2)*(1/(r^2-1))-(r+1/r)*(1/r)+2=0 := by
    field_simp
    ring
  have hdiff : (4-(r+1/r)^2)*
      (SemicirclePotential.resolventSquare (r+1/r)-1/(r^2-1))=0 := by
    nlinarith [hode,htest]
  have hcoeff : 4-(r+1/r)^2 ≠ 0 := ne_of_lt (by nlinarith)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hcoeff)

/-- The actual GOE contribution to the radial contact Hessian is
`−1/(y²−b_Q)`, equivalently `−1/[y²(1−ρ)]`. -/
theorem source_contact_resolventSquare_scaled (μ : FiniteMixture)
    {β x Q : ℝ} (h : Certificate μ β x Q) :
    SemicirclePotential.resolventSquare
      (markK μ β Q/Real.sqrt (markB μ Q))/(markB μ Q) =
        1/((markY β Q)^2-markB μ Q) := by
  obtain ⟨hr,he⟩ := sourceContact_geometric_ratio μ h
  have hy : 0 < markY β Q := markY_pos h.beta_pos h.overlap_range
  have hb : 0 < markB μ Q := markB_pos μ h.overlap_range.1
  have hs : 0 < Real.sqrt (markB μ Q) := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  have hgap : 0 < (markY β Q)^2-markB μ Q := by
    have hfrac := h.edge_margin.1
    exact sub_pos.mpr ((div_lt_one (sq_pos_of_pos hy)).mp hfrac)
  rw [he,resolventSquare_geometric hr]
  rw [div_pow,hs2]
  field_simp [hb.ne',hgap.ne']

/-- Exact source contact radial Hessian, obtained from the literal GOE
resolvent square and two-score precision. -/
theorem sourceRadialProfile_second_derivative_contact
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    deriv (sourceRadialProfileDerivative μ Q (markE μ β x Q))
      (markK μ β Q) =
        -sourceRadialCurvature μ Q-
          1/((markY β Q)^2-markB μ Q) := by
  have hk := sourceContact_markK_above_edge μ h
  rw [(sourceRadialProfileDerivative_hasDerivAt μ h.overlap_range.1
    (markE μ β x Q) (markK μ β Q) hk).deriv]
  change -sourceRadialCurvature μ Q-
    SemicirclePotential.resolventSquare
      (markK μ β Q/Real.sqrt (markB μ Q))/(markB μ Q)=_
  rw [source_contact_resolventSquare_scaled μ h]

private theorem negative_quadratic_of_det {A B D u v : ℝ}
    (hA : 0 < A) (hdet : B^2 < A*D) (hne : u ≠ 0 ∨ v ≠ 0) :
    -A*u^2+2*B*u*v-D*v^2 < 0 := by
  by_cases hv : v=0
  · have hu : u ≠ 0 := hne.resolve_right (by simp [hv])
    have hu2 : 0 < u^2 := sq_pos_of_ne_zero hu
    rw [hv]
    nlinarith [mul_pos hA hu2]
  · have hv2 : 0 < v^2 := sq_pos_of_ne_zero hv
    have hsum : 0 < (A*u-B*v)^2+(A*D-B^2)*v^2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sub_pos.mpr hdet) hv2)
    have hprod : 0 < A*(A*u^2-2*B*u*v+D*v^2) := by nlinarith [hsum]
    have hinner : 0 < A*u^2-2*B*u*v+D*v^2 := by
      by_contra hh
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hA.le (le_of_not_gt hh)
      linarith
    nlinarith [hinner]

/-- The contact Hessian entries printed in Lemma 12.15 form a strictly
negative quadratic form. The proof only needs the GOE radial term; the
additional positive score curvature strengthens the inequality. -/
theorem printed_mixed_contact_hessian_negative
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    {u v : ℝ} (hne : u ≠ 0 ∨ v ≠ 0) :
    let y := markY β Q
    let b := markB μ Q
    let ρ := b/y^2
    let C := profileConstant x Q
    let Hkk := -sourceRadialCurvature μ Q-1/(y^2-b)
    let Hka := β/Real.sqrt Q
    let Haa := -(1-ρ)*(1+Q-C*ρ)/(1-Q)^2
    Hkk*u^2+2*Hka*u*v+Haa*v^2 < 0 := by
  dsimp only
  let y := markY β Q
  let b := markB μ Q
  let ρ := b/y^2
  let C := profileConstant x Q
  let s := 1-Q
  let A := sourceRadialCurvature μ Q+1/(y^2-b)
  let B := β/Real.sqrt Q
  let D := (1-ρ)*(1+Q-C*ρ)/s^2
  have hy : 0 < y := markY_pos h.beta_pos h.overlap_range
  have hb : 0 < b := markB_pos μ h.overlap_range.1
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hq : 0 < Q := h.overlap_range.1
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hq
  have hρ : 0 < ρ := div_pos hb (sq_pos_of_pos hy)
  have hρ1 : ρ < 1 := h.edge_margin.1
  have hC0 : 0 < C := profileConstant_pos h.weight_range h.overlap_range
  have hC1 : C < 1 := by
    dsimp [C,profileConstant]
    nlinarith [mul_pos hq (sub_pos.mpr h.weight_range.2)]
  have hgap : 0 < y^2-b := by
    have := (div_lt_one (sq_pos_of_pos hy)).mp hρ1
    exact sub_pos.mpr this
  have hcurv : 0 < sourceRadialCurvature μ Q :=
    sourceRadialCurvature_pos μ hq hnp
  have hA : 0 < A := add_pos hcurv (one_div_pos.mpr hgap)
  have hD : 0 < D := by
    dsimp [D]
    apply div_pos
    · apply mul_pos (by linarith)
      nlinarith [mul_lt_mul_of_pos_right hρ1 hC0]
    · positivity
  have hrel : y=Q/(β*s) := rfl
  have hρrel : 1-ρ=(y^2-b)/y^2 := by
    dsimp [ρ]
    field_simp
  have hDEq : D/(y^2-b)=β^2*(1+Q-C*ρ)/Q^2 := by
    have hfirst : D/(y^2-b)=(1+Q-C*ρ)/(s^2*y^2) := by
      dsimp [D]
      rw [hρrel]
      field_simp [hgap.ne',(sq_pos_of_pos hy).ne']
    have hscale : 1/(s^2*y^2)=β^2/Q^2 := by
      rw [hrel]
      field_simp [h.beta_pos.ne',hs.ne',hq.ne']
    rw [hfirst]
    calc
      _=(1+Q-C*ρ)*(1/(s^2*y^2)) := by ring
      _=_ := by rw [hscale]; ring
  have hBsq : B^2=β^2/Q := by
    dsimp [B]
    rw [div_pow,Real.sq_sqrt hq.le]
  have hmargin : 0 < 1-C*ρ := by
    nlinarith [mul_lt_mul_of_pos_left hρ1 hC0]
  have hstrict : B^2 < D/(y^2-b) := by
    rw [hBsq,hDEq]
    have hβ2 : 0 < β^2 := sq_pos_of_pos h.beta_pos
    have hq2 : 0 < Q^2 := sq_pos_of_pos hq
    apply (div_lt_div_iff₀ hq hq2).mpr
    nlinarith [mul_pos hβ2 hmargin]
  have hdet : B^2 < A*D := by
    have hAlo : 1/(y^2-b) ≤ A := by dsimp [A]; linarith
    have hmul := mul_le_mul_of_nonneg_right hAlo hD.le
    have he : 1/(y^2-b)*D = D/(y^2-b) := by ring
    rw [he] at hmul
    exact hstrict.trans_le hmul
  have hneg := negative_quadratic_of_det hA hdet hne
  convert hneg using 1
  dsimp [A,B,D]
  ring

end
end SlowEquilibration.SphericalTAPMixedContactHessian
