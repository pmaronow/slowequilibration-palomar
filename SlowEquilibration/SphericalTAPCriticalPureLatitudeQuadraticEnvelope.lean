-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeBandMaximizer
public import SlowEquilibration.RadialQuadraticBounds

@[expose] public section

/-! A fixed-contact quadratic envelope for the proper-pure Palm exponent.
The energy derivative moves the slope, but the envelope remains centered at
the original contact latitude. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeQuadraticEnvelope
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeUniformCurvature
open SphericalTAPCriticalPureLatitudeContactStationarity
open SlowEquilibration.RadialQuadraticBounds
set_option autoImplicit false

/-- Integrate a strict curvature upper bound about a point whose derivative
need not vanish. -/
theorem quadratic_tangent_upper {f g g' : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) (hf : ∀ x∈D,HasDerivAt f (g x) x)
    (hg : ∀ x∈D,HasDerivAt g (g' x) x) {c m : ℝ} (hm : m∈D)
    (hSecond : ∀ x∈D,g' x ≤ -c) :
    ∀ x∈D, f x ≤ f m+g m*(x-m)-c/2*(x-m)^2 := by
  let F := fun x : ℝ => f x-g m*(x-m)
  let G := fun x : ℝ => g x-g m
  have hF (x : ℝ) (hx : x∈D) : HasDerivAt F (G x) x := by
    convert (hf x hx).sub (((hasDerivAt_id x).sub_const m).const_mul (g m)) using 1
    · rfl
    · dsimp [G]; ring
  have hG (x : ℝ) (hx : x∈D) : HasDerivAt G (g' x) x := by
    exact (hg x hx).sub_const (g m)
  have hh := quadratic_upper_of_second_derivative hD hF hG hm
    (by simp [G]) hSecond
  intro x hx
  have h := hh x hx
  dsimp [F] at h
  simp only [sub_self,mul_zero,sub_zero] at h
  linarith

/-- At the contact latitude, varying energy changes the latitude slope by
exactly `β p (e-E)/sqrt Q`. -/
theorem sourcePureLatitudeExponent_contact_slope_at_energy
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    (e : ℝ) :
    sourcePureLatitudeExponentSlope p alpha Q β e (Real.sqrt Q) =
      β*(p:ℝ)/Real.sqrt Q*
        (e-markE (FiniteMixture.pure p hp alpha halpha) β x Q) := by
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  have hq : q ≠ 0 := (Real.sqrt_pos.mpr h.overlap_range.1).ne'
  have hqmem : q ∈ Ioo (-1:ℝ) 1 := by
    have hq1 : q < 1 := by
      dsimp [q]
      rw [←Real.sqrt_one]
      exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
    exact ⟨by have hq0 := Real.sqrt_pos.mpr h.overlap_range.1; linarith,hq1⟩
  have hzero := sourcePureLatitudeExponent_contact_deriv_zero p hp alpha halpha h
  rw [(sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β E q
    h.overlap_range.1 hqmem).deriv] at hzero
  have hroot : (q/Real.sqrt Q)^(p-1)=1 := by
    dsimp [q]
    rw [div_self hq]
    simp
  calc
    sourcePureLatitudeExponentSlope p alpha Q β e q =
        sourcePureLatitudeExponentSlope p alpha Q β E q+
          β*(p:ℝ)/q*(e-E) := by
      unfold sourcePureLatitudeExponentSlope
      rw [hroot]
      ring
    _ = _ := by rw [hzero]; ring

/-- The literal exponent has a Gaussian envelope about the fixed contact
latitude, with only a quadratic energy correction. -/
theorem sourcePureLatitudeExponent_contact_quadratic_envelope
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
    let q := Real.sqrt Q
    ∃ ε b c C₂ : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 < c ∧ 0 ≤ C₂ ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      ∀ e ∈ Icc (E-ε) (E+ε), ∀ a ∈ Icc (q-b) (q+b),
        sourcePureLatitudeExponent p alpha Q β e a ≤
          sourcePureLatitudeExponent p alpha Q β E q+
            β*(e-E)+C₂*(e-E)^2-c/4*(a-q)^2 := by
  dsimp only
  obtain ⟨ε,b,c,hε,hb,hbq,hc,hband,hcurv⟩ :=
    sourcePureLatitudeExponent_uniform_negative_curvature p hp alpha halpha h
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  let B := β*(p:ℝ)/q
  let C₂ := B^2/c
  have hC : 0 ≤ C₂ := div_nonneg (sq_nonneg _) hc.le
  refine ⟨ε,b,c,C₂,hε,hb,hbq,hc,hC,hband,?_⟩
  intro e he a ha
  let D : Set ℝ := Icc (q-b) (q+b)
  have hqD : q ∈ D := by
    change q-b ≤ q ∧ q ≤ q+b
    constructor <;> linarith
  have hcurv' : ∀ t∈D,
      sourcePureLatitudeExponentCurvature p alpha Q β e t ≤ -c := by
    intro t ht
    rw [←sourcePureLatitudeExponent_second_deriv p hp alpha Q β e t
      h.overlap_range.1 (hband ht)]
    exact hcurv e he t ht
  have htangent := quadratic_tangent_upper (D := D)
    (f := sourcePureLatitudeExponent p alpha Q β e)
    (g := sourcePureLatitudeExponentSlope p alpha Q β e)
    (g' := sourcePureLatitudeExponentCurvature p alpha Q β e)
    (convex_Icc _ _)
    (fun t ht => sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β e t
      h.overlap_range.1 (hband ht))
    (fun t ht => sourcePureLatitudeExponentSlope_hasDerivAt p hp alpha Q β e t
      h.overlap_range.1 (hband ht)) hqD hcurv' a ha
  have hslope := sourcePureLatitudeExponent_contact_slope_at_energy
    p hp alpha halpha h e
  have hvalue : sourcePureLatitudeExponent p alpha Q β e q =
      sourcePureLatitudeExponent p alpha Q β E q+β*(e-E) := by
    unfold sourcePureLatitudeExponent
    have hq : q ≠ 0 := (Real.sqrt_pos.mpr h.overlap_range.1).ne'
    have hr : (q/Real.sqrt Q)^p=1 := by
      dsimp [q]
      rw [div_self hq]
      simp
    rw [hr]
    ring
  rw [hslope,hvalue] at htangent
  have hyoung : B*(e-E)*(a-q)-c/2*(a-q)^2 ≤
      C₂*(e-E)^2-c/4*(a-q)^2 := by
    have hs : 0 ≤ (B*(e-E)-c/2*(a-q))^2 := sq_nonneg _
    dsimp [C₂]
    have hmul : c*(B*(e-E)*(a-q)-c/4*(a-q)^2) ≤ B^2*(e-E)^2 := by
      nlinarith [hs]
    have hdiv : B*(e-E)*(a-q)-c/4*(a-q)^2 ≤ B^2*(e-E)^2/c :=
      (le_div_iff₀ hc).2 (by nlinarith [hmul])
    have hdiv' : B*(e-E)*(a-q)-c/4*(a-q)^2 ≤ B^2/c*(e-E)^2 := by
      convert hdiv using 1; ring
    have hnonneg : 0 ≤ c/4*(a-q)^2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith [hdiv']
  calc
    _ ≤ sourcePureLatitudeExponent p alpha Q β E q+β*(e-E)+
        B*(e-E)*(a-q)-c/2*(a-q)^2 := by
          dsimp [B] at *
          exact htangent
    _ ≤ _ := by linarith

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeQuadraticEnvelope
