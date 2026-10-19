-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapLatitudeFactor
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactCurvature

@[expose] public section

/-! Global monotonicity of the normalized pure latitude exponent to the
right of its actual contact, derived from the source scalar factorization. -/

namespace SlowEquilibration.SphericalPureCapLatitudeRightSaddle
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeContactStationarity
open SphericalTAPCriticalPureLatitudeContactSign
open SphericalPureCapLatitudeFactor
open SphericalMarkedWindows
set_option autoImplicit false

private theorem capAux_strictAntiOn_upper_interval
    (p : ℕ) (hp : 4 ≤ p) {β r : ℝ} (hβ : 0 < β)
    (hr0 : 0 ≤ r)
    (hr : (p:ℝ)*r^2 ≥ (p:ℝ)-2) :
    StrictAntiOn (capAux p β) (Icc r 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop [capAux])
  intro a ha
  have ha' : a ∈ Ioo r (1:ℝ) := by simpa only [interior_Icc] using ha
  have ha0 : 0 < a := lt_of_le_of_lt hr0 ha'.1
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hsq : r^2 < a^2 := by nlinarith [ha'.1,hr0]
  have hfac : (p:ℝ)-2-(p:ℝ)*a^2 < 0 := by
    nlinarith [mul_pos hp0 (sub_pos.mpr hsq)]
  rw [(capAux_hasDerivAt p hp β a).deriv]
  exact mul_neg_of_pos_of_neg (mul_pos hβ (pow_pos ha0 _)) hfac

/-- The auxiliary factor is strictly decreasing from a source threshold
strictly below the contact all the way to the pole. -/
theorem capAux_strictAntiOn_from_pure_contact
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let q := Real.sqrt Q
    let r := Real.sqrt (((p:ℝ)-2)/(p:ℝ))
    0 ≤ r ∧ r < q ∧ StrictAntiOn (capAux p β) (Icc r 1) := by
  dsimp only
  let q := Real.sqrt Q
  let r := Real.sqrt (((p:ℝ)-2)/(p:ℝ))
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (0:ℝ) ≤ (p:ℝ)-2 := by
    have hpR : (4:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hrSq : r^2=((p:ℝ)-2)/(p:ℝ) := Real.sq_sqrt (div_nonneg hp2 hp0.le)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hqSq : q^2=Q := Real.sq_sqrt h.overlap_range.1.le
  have hcontact := pure_contact_latitude_factor_pos p (by omega) 1 (by positivity) h
  have hrqSq : r^2 < q^2 := by
    rw [hrSq,hqSq]
    exact (div_lt_iff₀ hp0).mpr (by nlinarith [hcontact])
  have hrq : r < q := by nlinarith [Real.sqrt_nonneg Q]
  have hr : (p:ℝ)*r^2 ≥ (p:ℝ)-2 := by
    rw [hrSq]
    field_simp [hp0.ne']
    exact le_refl _
  exact ⟨hr0,hrq,capAux_strictAntiOn_upper_interval p hp h.beta_pos hr0 hr⟩

/-- The contact root of the derivative polynomial is on its increasing
branch; this is the exact scalar consequence of the strict Hessian edge. -/
theorem capPolynomial_contact_increasing_branch
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let E := markE μ β x Q
    let e := E/q^p
    let f := capAux p β q
    capPolynomial p e f = 0 ∧
      0 < (p:ℝ)*e-2*(p:ℝ)*((p:ℝ)-1)*f := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let E := markE μ β x Q
  let e := E/q^p
  let f := capAux p β q
  let B := markB μ Q
  let s := 1-Q
  have hq : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hqSq : q^2=Q := Real.sq_sqrt h.overlap_range.1.le
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hEeq : E=e*q^p := by dsimp [e]; field_simp [pow_ne_zero p hq.ne']
  have hqmem : q ∈ Ioo (0:ℝ) 1 := by
    constructor
    · exact hq
    · rw [←Real.sqrt_one]
      exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hzero := sourcePureLatitudeExponent_contact_deriv_zero
    p (by omega) 1 (by positivity) h
  rw [(sourcePureLatitudeExponent_hasDerivAt p (by omega) 1 Q β E q
    h.overlap_range.1 ⟨by linarith [hq],hqmem.2⟩).deriv] at hzero
  have hfactor := sourcePureLatitudeExponent_slope_factor p hp
    h.overlap_range.1 β e q hqmem
  rw [←hEeq] at hfactor
  rw [hfactor] at hzero
  have hP0 : capPolynomial p e f=0 := by
    have hcoef : q/(1-q^2) ≠ 0 := div_ne_zero hq.ne'
      (by rw [hqSq]; exact hs.ne')
    exact (mul_eq_zero.mp hzero).resolve_left hcoef
  have hB : B=(p:ℝ)*((p:ℝ)-1)*Q^p := by
    dsimp [B]
    rw [(sourcePure_contact_covariance_scalars p (by omega) 1 (by positivity) Q).2]
    rw [FiniteMixture.pure_xi]
    ring
  have hK := sourcePure_contact_radial_graph
    p (by omega) 1 (by positivity) h
  change markK μ β Q=(p:ℝ)*E at hK
  have hEmark : β*(p:ℝ)*E=Q/s+β^2*B*s/Q := by
    calc
      β*(p:ℝ)*E=β*markK μ β Q := by rw [hK]; ring
      _=β*(markY β Q+B/markY β Q) := by rfl
      _=Q/s+β^2*B*s/Q := by
        dsimp [markY,s]
        field_simp [h.beta_pos.ne',h.overlap_range.1.ne',hs.ne']
  have hρeq : B/(markY β Q)^2=β^2*B*s^2/Q^2 := by
    dsimp [markY,s]
    field_simp [h.beta_pos.ne',h.overlap_range.1.ne',hs.ne']
  have hmargin : 0 < Q/s-β^2*B*s/Q := by
    have hρ : β^2*B*s^2/Q^2 < 1 := by rw [←hρeq]; exact h.edge_margin.1
    have hh := mul_pos (div_pos h.overlap_range.1 hs)
      (sub_pos.mpr hρ)
    have heq : (Q/s)*(1-β^2*B*s^2/Q^2)=Q/s-β^2*B*s/Q := by
      field_simp [h.overlap_range.1.ne',hs.ne']
    rw [heq] at hh
    exact hh
  have hpow : q^p*q^(p-2)=Q^(p-1) := by
    calc
      q^p*q^(p-2)=q^(2*p-2) := by rw [←pow_add]; congr 1; omega
      _=(q^2)^(p-1) := by
        rw [show 2*p-2=2*(p-1) by omega,pow_mul]
      _=_ := by rw [hqSq]
  have hpowQ : Q^(p-1)*Q=Q^p := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have heq : β*q^p*((p:ℝ)*e-2*(p:ℝ)*((p:ℝ)-1)*f)=
      Q/s-β^2*B*s/Q := by
    dsimp [f,capAux]
    rw [hqSq]
    calc
      _ = β*(p:ℝ)*E-2*β^2*(p:ℝ)*((p:ℝ)-1)*Q^(p-1)*s := by
        rw [hEeq,←hpow]
        ring
      _ = _ := by
        rw [hEmark,hB]
        rw [←hpowQ]
        field_simp [h.overlap_range.1.ne',hs.ne']
        ring
  refine ⟨hP0,?_⟩
  have hpos : 0 < β*q^p := mul_pos h.beta_pos (pow_pos hq _)
  have hh := (mul_pos_iff_of_pos_left hpos).mp (heq ▸ hmargin)
  exact hh

/-- The pure source contact is the unique decreasing-side saddle all the
way to latitude one, not merely on a small band. -/
theorem sourcePureLatitudeExponent_strictAntiOn_right_of_contact
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let q := Real.sqrt Q
    StrictAntiOn (sourcePureLatitudeExponent p 1 Q β E) (Ico q 1) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let q := Real.sqrt Q
  let e := E/q^p
  let f := capAux p β q
  obtain ⟨hr0,hrq,hantiF⟩ := capAux_strictAntiOn_from_pure_contact p hp h
  obtain ⟨hP0,hbranch⟩ := capPolynomial_contact_increasing_branch p hp h
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    rw [←Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hEeq : E=e*q^p := by
    dsimp [e]
    field_simp [pow_ne_zero p hq0.ne']
  have hderiv : ∀ a ∈ Ioo q 1,
      deriv (sourcePureLatitudeExponent p 1 Q β E) a < 0 := by
    intro a ha
    have ha0 : 0 < a := lt_trans hq0 ha.1
    have haR : a ∈ Icc (Real.sqrt (((p:ℝ)-2)/(p:ℝ))) 1 :=
      ⟨by linarith [hrq,ha.1],ha.2.le⟩
    have hqR : q ∈ Icc (Real.sqrt (((p:ℝ)-2)/(p:ℝ))) 1 :=
      ⟨hrq.le,hq1.le⟩
    have hfLt : capAux p β a < f := hantiF hqR haR ha.1
    have hpR : 0 < (p:ℝ)*((p:ℝ)-1) := by
      have hP : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hp4 : (4:ℝ) ≤ p := by exact_mod_cast hp
      exact mul_pos hP (by linarith)
    have hbracket : 0 < (p:ℝ)*e-
        (p:ℝ)*((p:ℝ)-1)*(capAux p β a+f) := by
      nlinarith [mul_pos hpR (sub_pos.mpr hfLt)]
    have hpoly : capPolynomial p e (capAux p β a) < 0 := by
      have heq : capPolynomial p e (capAux p β a)=
          (capAux p β a-f)*
            ((p:ℝ)*e-(p:ℝ)*((p:ℝ)-1)*(capAux p β a+f)) := by
        calc
          capPolynomial p e (capAux p β a) =
              capPolynomial p e (capAux p β a)-capPolynomial p e f := by
                rw [hP0]; ring
          _ = _ := by dsimp [capPolynomial]; ring
      rw [heq]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hfLt) hbracket
    have hcoef : 0 < a/(1-a^2) := by
      apply div_pos ha0
      nlinarith [ha0,ha.2]
    rw [(sourcePureLatitudeExponent_hasDerivAt p (by omega) 1 Q β E a
      h.overlap_range.1 ⟨by linarith [ha0],ha.2⟩).deriv]
    rw [hEeq]
    rw [sourcePureLatitudeExponent_slope_factor p hp h.overlap_range.1 β e a
      ⟨ha0,ha.2⟩]
    exact mul_neg_of_pos_of_neg hcoef hpoly
  apply strictAntiOn_of_deriv_neg (convex_Ico _ _) ?_ ?_
  · intro a ha
    exact (sourcePureLatitudeExponent_hasDerivAt p (by omega) 1 Q β E a
      h.overlap_range.1 ⟨by have := ha.1; linarith [hq0],ha.2⟩).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : a ∈ Ioo q 1 := by simpa only [interior_Ico] using ha
    exact hderiv a ha'

end
end SlowEquilibration.SphericalPureCapLatitudeRightSaddle
