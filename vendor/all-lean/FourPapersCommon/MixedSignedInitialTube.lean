module
public import FourPapersCommon.MixedSignedInitialLocal
public import FourPapersCommon.MixtureCoercivity

@[expose] public section

/-! A system-size independent genuine mixed pressure gap across the signed
first breakpoint. The trial covariance remains fixed while the physical
constraint varies on both sides of the breakpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 900000

 theorem exists_mixed_constrainedPhi_signed_initial_breakpoint_tube_of_curvature
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {t₀ e : ℝ} (ht₀ : t₀<1) (hq1 : 0<s.q 1) (he : 0 ≤ e)
    (he_small : e ≤ (1-t₀)/2)
    (hR : ξ.second (s.q 1)*section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1+e) :
    ∃ rho > (0:ℝ), ∃ delta > (0:ℝ),
      ∀ t∈Icc (0:ℝ) t₀,∀ u∈Icc (-1:ℝ) 0,|u-(-s.q 1)| ≤ rho→
      ∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u ≤
        2*mixedInterpolationPsi ξ s h t-delta := by
  let D : ℝ := (1-t₀)^2/8*(s.q 1)^2
  have hD : 0<D := by
    dsimp [D]
    exact mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num)) (sq_pos_of_pos hq1)
  let K := ξ.second 1
  have hK : 0 ≤ K := ξ.second_nonneg 1
  let rho : ℝ := min 1 (D/(8*(1+K)))
  have hden : 0<8*(1+K) := by positivity
  have hrho : 0<rho := lt_min (by norm_num) (div_pos hD hden)
  refine ⟨rho,hrho,D/2,div_pos hD (by norm_num),?_⟩
  intro t ht u hu hutube Ω _ _ n hn sk hatt
  obtain ⟨σ,τ,hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ,τ),hστ⟩⟩
  have ht1 : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans ht₀.le⟩
  have hv : -s.q 1∈Icc (-s.q 1) 0 := ⟨le_rfl,neg_nonpos.mpr hq1.le⟩
  obtain ⟨ell,hell,HL⟩ := mixedSignedInitial_scalar_gain_bounded ξ s h ht ht₀ hv he he_small hR
  have HH := mixedSignedInitial_constrainedPhi_le hn ξ s h sk (v:=-s.q 1) ht1 hu hv ell
  have hq1top := s.q_le_one (p:=1) (by omega)
  have HT := ξ.tangentRemainder_quadratic_upper
    (show u∈Icc (-1:ℝ) 1 from ⟨hu.1,hu.2.trans zero_le_one⟩)
    (show -s.q 1∈Icc (-1:ℝ) 1 from ⟨by linarith,by linarith⟩)
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hrhoD : rho ≤ D/(8*(1+K)) := min_le_right _ _
  have Hlin : -(ell*(u-(-s.q 1))) ≤ 2*rho := by
    have Habs : |ell*(u-(-s.q 1))| ≤ 2*rho := by
      rw [abs_mul]
      exact mul_le_mul hell hutube (abs_nonneg _) (by norm_num)
    exact (neg_le_abs _).trans Habs
  have hsq : (u-(-s.q 1))^2 ≤ rho^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hrho.le).mpr hutube
  have hrhosq : rho^2 ≤ rho := by nlinarith only [hrho.le,hrho1]
  have Hrem : t*ξ.tangentRemainder u (-s.q 1) ≤ K*rho := by
    have H1 := mul_le_mul_of_nonneg_left HT ht.1
    have H2 := mul_le_of_le_one_left (mul_nonneg hK (sq_nonneg (u-(-s.q 1)))) ht1.2
    have H3 := mul_le_mul_of_nonneg_left (hsq.trans hrhosq) hK
    change t*ξ.tangentRemainder u (-s.q 1) ≤ _
    change t*ξ.tangentRemainder u (-s.q 1) ≤ t*(K*(u-(-s.q 1))^2) at H1
    nlinarith only [H1,H2,H3]
  have Herr : 2*rho+K*rho ≤ D/4 := by
    have HR := (le_div_iff₀ hden).mp hrhoD
    have HK := mul_nonneg hK hrho.le
    nlinarith only [HR,HK]
  have Htransport :
      section5RetainedSignedInitialV (mixedClockScheme ξ s) (mixedBeta ξ) h
        (t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock (-s.q 1))))
        ((1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
        (t*((mixedBeta ξ)^2*(-ξ.clock (-s.q 1)))) ell-ell*u ≤
      2*parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k+2) h-D+2*rho := by
    rw [neg_sq] at HL
    change _ ≤ 2*parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k+2) h-D at HL
    linarith only [HL,Hlin]
  dsimp [mixedInterpolationPsi]
  linarith only [HH,Htransport,Hrem,Herr,hD.le]

 theorem exists_mixed_constrainedPhi_signed_initial_breakpoint_tube
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : s.m 0<s.m 1) (hq1 : 0<s.q 1) (hright : s.q 1<s.q 2 ∨ s.q 1=1)
    {t₀ : ℝ} (ht₀ : t₀<1)
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h+ε)
    (hsmall : mixedLocalLeftConstant ξ*ε^(1/6:ℝ) ≤ 1-t₀) :
    ∃ rho > (0:ℝ),∃ delta > (0:ℝ),
      ∀ t∈Icc (0:ℝ) t₀,∀ u∈Icc (-1:ℝ) 0,|u-(-s.q 1)| ≤ rho→
      ∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u ≤
        2*mixedInterpolationPsi ξ s h t-delta := by
  obtain ⟨e,he,hes,HR⟩ := mixed_initial_curvature_data_of_near_minimum ξ s h ε
    hm hq1 hright ht₀ hmin hnear hsmall
  exact exists_mixed_constrainedPhi_signed_initial_breakpoint_tube_of_curvature
    ξ s h ht₀ hq1 he hes HR

end FourPapersCommon
