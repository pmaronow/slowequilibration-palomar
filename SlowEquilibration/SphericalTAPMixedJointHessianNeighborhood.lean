-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedJointHessianContinuity

@[expose] public section

/-! The literal mixed `(k,a)` Hessian is uniformly negative definite on
one fixed neighborhood of the source contact mark. -/

namespace SlowEquilibration.SphericalTAPMixedJointHessianNeighborhood
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPMixedBandExponent
open SphericalTAPMixedActualRadialHessian
open SphericalTAPMixedActualLatitudeHessian
open SphericalTAPMixedJointHessianContinuity
open SphericalTAPMixedJointLatitudeContinuity
open scoped Topology
set_option autoImplicit false

def actualMixedHkk (μ : FiniteMixture) (β Q : ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv (deriv (fun kk => sourceMixedBandExponent μ β Q z.1.1 kk z.2)) z.1.2

def actualMixedHka (μ : FiniteMixture) (β Q : ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv (fun t => deriv
    (fun kk => sourceMixedBandExponent μ β Q z.1.1 kk t) z.1.2) z.2

def actualMixedHaa (μ : FiniteMixture) (β Q : ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv (deriv (sourceMixedBandExponent μ β Q z.1.1 z.1.2)) z.2

private theorem contact_entries (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let z0 : (ℝ × ℝ) × ℝ := ((markE μ β x Q,markK μ β Q),Real.sqrt Q)
    actualMixedHkk μ β Q z0 =
        -sourceRadialCurvature μ Q-
          1/((markY β Q)^2-markB μ Q) ∧
    actualMixedHka μ β Q z0 = β/Real.sqrt Q ∧
    actualMixedHaa μ β Q z0 =
      -(1-markB μ Q/(markY β Q)^2)*
        (1+Q-profileConstant x Q*(markB μ Q/(markY β Q)^2))/(1-Q)^2 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact sourceMixedBandExponent_radial_second_contact μ h (Real.sqrt Q)
  · rw [actualMixedHka,sourceMixedBandExponent_radial_latitude μ β
      h.overlap_range.1 (markE μ β x Q) (markK μ β Q) (Real.sqrt Q)
      (sourceContact_markK_above_edge μ h)]
    rw [(SphericalTAPMixedContactDerivatives.mixed_regression_row_derivative_contact
      μ h.overlap_range.1 hnp).2]
    ring
  · exact sourceMixedBandExponent_latitude_second_contact μ h hnp

private theorem strict_det_of_negative_form {A B D : ℝ} (hA : 0 < A)
    (hneg : ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
      -A*u^2+2*B*u*v-D*v^2 < 0) : B^2 < A*D := by
  have htest := hneg (B/A) 1 (Or.inr one_ne_zero)
  have heq : (-A*(B/A)^2+2*B*(B/A)*1-D*1^2)*A=B^2-A*D := by
    field_simp [hA.ne']
    ring
  have hh : (-A*(B/A)^2+2*B*(B/A)*1-D*1^2)*A < 0 :=
    mul_neg_of_neg_of_pos htest hA
  rw [heq] at hh
  linarith

private theorem quantitative_negative_form {A B D d M u v : ℝ}
    (hA : 0 < A) (hd : 0 < d) (hM : 0 < M)
    (hdet : d ≤ A*D-B^2) (htrace : A+D ≤ M) :
    -A*u^2+2*B*u*v-D*v^2 ≤ -(d/M)*(u^2+v^2) := by
  let p := A*u^2-2*B*u*v+D*v^2
  have hn : 0 ≤ u^2+v^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hiden : (A+D)*p =
      (A*D-B^2)*(u^2+v^2)+(A*u-B*v)^2+(B*u-D*v)^2 := by
    dsimp [p]
    ring
  have hdet0 : 0 ≤ A*D-B^2 := le_trans hd.le hdet
  have htrace0 : 0 < A+D := by
    have hAD : 0 < A*D := lt_of_lt_of_le (by positivity : 0 < B^2+d) (by linarith [hdet])
    have hD : 0 < D := (mul_pos_iff_of_pos_left hA).mp hAD
    linarith
  have hp : 0 ≤ p := by
    have hh : 0 ≤ (A+D)*p := by rw [hiden]; positivity
    exact (mul_nonneg_iff_of_pos_left htrace0).mp hh
  have hlow : d*(u^2+v^2) ≤ (A+D)*p := by
    rw [hiden]
    have hh := mul_nonneg (sub_nonneg.mpr hdet) hn
    nlinarith [sq_nonneg (A*u-B*v),sq_nonneg (B*u-D*v)]
  have hup : (A+D)*p ≤ M*p := mul_le_mul_of_nonneg_right htrace hp
  have hup' : (A+D)*p ≤ p*M := by nlinarith [hup]
  have hratio : (d/M)*(u^2+v^2) ≤ p := by
    calc
      (d/M)*(u^2+v^2) = (d*(u^2+v^2))/M := by ring
      _ ≤ p := (div_le_iff₀ hM).mpr (hlow.trans hup')
  dsimp [p] at hratio
  linarith

/-- One source-chosen box has a uniform strictly negative quadratic bound
for the actual `(k,a)` Hessian of the literal mixed exponent. The box also
stays inside the physical latitude and exterior GOE domains. -/
theorem actual_mixed_hessian_uniform_negative_neighborhood
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ ε0 b0 cstar : ℝ, 0 < ε0 ∧ 0 < b0 ∧ 0 < cstar ∧
      ∀ e k a : ℝ, |e-E| ≤ ε0 → |k-K| ≤ ε0 → |a-q| ≤ b0 →
        edge < k ∧ |a| < 1 ∧
          ∀ u v : ℝ,
            actualMixedHkk μ β Q ((e,k),a)*u^2+
              2*actualMixedHka μ β Q ((e,k),a)*u*v+
              actualMixedHaa μ β Q ((e,k),a)*v^2 ≤
                -cstar*(u^2+v^2) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  let z0 : (ℝ × ℝ) × ℝ := ((E,K),q)
  let A : (ℝ × ℝ) × ℝ → ℝ := fun z => -actualMixedHkk μ β Q z
  let B : (ℝ × ℝ) × ℝ → ℝ := fun z => actualMixedHka μ β Q z
  let D : (ℝ × ℝ) × ℝ → ℝ := fun z => -actualMixedHaa μ β Q z
  let Δ : (ℝ × ℝ) × ℝ → ℝ := fun z => A z*D z-(B z)^2
  let T : (ℝ × ℝ) × ℝ → ℝ := fun z => A z+D z
  obtain ⟨hkk,hka,haa⟩ := contact_entries μ h hnp
  have hA0 : 0 < A z0 := by
    have hy : 0 < markY β Q := markY_pos h.beta_pos h.overlap_range
    have hb : 0 < markB μ Q := markB_pos μ h.overlap_range.1
    have hgap : 0 < (markY β Q)^2-markB μ Q := by
      have hh := (div_lt_one (sq_pos_of_pos hy)).mp h.edge_margin.1
      exact sub_pos.mpr hh
    have hcurv := sourceRadialCurvature_pos μ h.overlap_range.1 hnp
    dsimp [A,z0,E,K,q]
    rw [hkk]
    nlinarith [one_div_pos.mpr hgap]
  have hneg : ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
      -A z0*u^2+2*B z0*u*v-D z0*v^2 < 0 := by
    intro u v huv
    dsimp [A,B,D,z0,E,K,q]
    rw [hkk,hka,haa]
    convert (SphericalTAPMixedContactHessian.printed_mixed_contact_hessian_negative
      μ h hnp huv) using 1
    ring
  have hD0 : 0 < D z0 := by
    have hh := hneg 0 1 (Or.inr one_ne_zero)
    nlinarith [hh]
  have hΔ0 : 0 < Δ z0 := by
    dsimp only [Δ]
    exact sub_pos.mpr (strict_det_of_negative_form hA0 hneg)
  have hT0 : 0 < T z0 := by dsimp [T]; linarith [hA0,hD0]
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hHkk : ContinuousAt (actualMixedHkk μ β Q) z0 :=
    sourceMixedBandExponent_radial_second_joint_continuousAt μ β
      h.overlap_range.1 E K q (sourceContact_markK_above_edge μ h)
  have hHka : ContinuousAt (actualMixedHka μ β Q) z0 :=
    sourceMixedBandExponent_radial_latitude_joint_continuousAt μ β
      h.overlap_range.1 E K q (sourceContact_markK_above_edge μ h)
  have hHaa : ContinuousAt (actualMixedHaa μ β Q) z0 :=
    sourceMixedBandExponent_latitude_second_joint_continuousAt μ β Q E K q
      (abs_lt.mpr (by constructor <;> linarith))
  have hAcont : ContinuousAt A z0 := hHkk.neg
  have hBcont : ContinuousAt B z0 := hHka
  have hDcont : ContinuousAt D z0 := hHaa.neg
  have hΔcont : ContinuousAt Δ z0 := by
    dsimp [Δ]
    fun_prop (disch := assumption)
  have hTcont : ContinuousAt T z0 := by
    dsimp [T]
    fun_prop (disch := assumption)
  let cA := A z0/2
  let d := Δ z0/2
  let M := 2*T z0
  have hcA : 0 < cA := by dsimp [cA]; linarith [hA0]
  have hd : 0 < d := by dsimp [d]; linarith [hΔ0]
  have hM : 0 < M := by dsimp [M]; linarith [hT0]
  have hcAlt : cA < A z0 := by change A z0/2 < A z0; linarith [hA0]
  have hdlt : d < Δ z0 := by change Δ z0/2 < Δ z0; linarith [hΔ0]
  have hTlt : T z0 < M := by change T z0 < 2*T z0; linarith [hT0]
  have hEvA : ∀ᶠ z in 𝓝 z0, cA < A z :=
    hAcont.tendsto.eventually (lt_mem_nhds hcAlt)
  have hEvΔ : ∀ᶠ z in 𝓝 z0, d < Δ z :=
    hΔcont.tendsto.eventually (lt_mem_nhds hdlt)
  have hEvT : ∀ᶠ z in 𝓝 z0, T z < M :=
    hTcont.tendsto.eventually (gt_mem_nhds hTlt)
  have hkproj : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) :=
    continuous_snd.comp continuous_fst
  have haproj : Continuous (fun z : (ℝ × ℝ) × ℝ => z.2) := continuous_snd
  have hEvK : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0, edge < z.1.2 :=
    hkproj.continuousAt.eventually (isOpen_Ioi.mem_nhds
      (show edge < K from sourceContact_markK_above_edge μ h))
  have hEvLat : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0, |z.2| < 1 := by
    have hh : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0,
        z.2 ∈ Ioo (-1 : ℝ) 1 :=
      haproj.continuousAt.eventually (isOpen_Ioo.mem_nhds
        (show q ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith))
    filter_upwards [hh] with z hz
    exact abs_lt.mpr hz
  have hevent : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0,
      cA < A z ∧ d < Δ z ∧ T z < M ∧ edge < z.1.2 ∧ |z.2| < 1 := by
    filter_upwards [hEvA,hEvΔ,hEvT,hEvK,hEvLat] with z h1 h2 h3 h4 h5
    exact ⟨h1,h2,h3,h4,h5⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε0 := r/2
  let b0 := r/2
  let cstar := d/M
  have hε0 : 0 < ε0 := by dsimp [ε0]; linarith
  have hb0 : 0 < b0 := by dsimp [b0]; linarith
  have hcstar : 0 < cstar := div_pos hd hM
  refine ⟨ε0,b0,cstar,hε0,hb0,hcstar,?_⟩
  intro ee kk aa he hk ha
  have hdist : dist (((ee,kk),aa)) z0 < r := by
    dsimp [z0]
    simp only [Prod.dist_eq,Real.dist_eq]
    apply max_lt
    · apply max_lt
      · have hh := (abs_le.mp he).2
        dsimp [ε0,E] at *
        linarith
      · have hh := (abs_le.mp hk).2
        dsimp [ε0,K] at *
        linarith
    · have hh := (abs_le.mp ha).2
      dsimp [b0,q] at *
      linarith
  obtain ⟨hAz,hΔz,hTz,hkz,haz⟩ := hball hdist
  refine ⟨hkz,haz,?_⟩
  intro u v
  have hApos : 0 < A ((ee,kk),aa) := lt_trans hcA hAz
  have hbound := quantitative_negative_form hApos hd hM hΔz.le hTz.le
    (u := u) (v := v)
  simpa [A,B,D,cstar] using hbound

end
end SlowEquilibration.SphericalTAPMixedJointHessianNeighborhood
