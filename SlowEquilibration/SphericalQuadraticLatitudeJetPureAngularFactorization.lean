-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureWeightedPoint
public import SlowEquilibration.SphericalQuadraticLatitudeJetPurePalmFactorization
public import SlowEquilibration.PositiveAngularFactorization

@[expose] public section

/-! Tonelli/Fubini lifts the exact proper-pure pointwise residual
factorization to the physical angular latitude partition. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open ConditionedDeterminantMoments SphericalTAPCriticalAnalyticNeighborhood
open SphericalTAPPurePalmDeterminantQuadraticReduction
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem pure_palm_determinant_latitude_angular_factorization
    {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (hμ : 3 ≤ (FiniteMixture.pure p hp alpha halpha).minDegree)
    {Q : ℝ} (hQ : 0 < Q) (a β : ℝ) (ha : 0 ≤ 1-a^2)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e c : ℝ)
    (hpointInt : ∀ y : Vector (d+1),
      Integrable (fun J =>
        intrinsicDet (FiniteMixture.pure p hp alpha halpha) Q u J *
          originalLatitudeBankPoint (FiniteMixture.pure p hp alpha halpha) a β u J y)
        (pureLaw p hp alpha halpha Q u hu e))
    (hres : ∀ y : Vector (d+1), ‖y‖^2=((d+1:ℕ):ℝ) →
      (∫ J, Real.exp (β*(field
          (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) J
          (originalLatitudePoint a u (quadraticBankDirection (d+1) u y)) -
        quadraticLatitudeJet (FiniteMixture.pure p hp alpha halpha) a u
          (quadraticBankDirection (d+1) u y) J))
        ∂pureLaw p hp alpha halpha Q u hu e) = c)
    (hbankInt : Integrable (fun J =>
      intrinsicDet (FiniteMixture.pure p hp alpha halpha) Q u J *
        quadraticBankPartition (FiniteMixture.pure p hp alpha halpha) a β u J)
      (pureLaw p hp alpha halpha Q u hu e)) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Integrable (fun J => intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J)
      (pureLaw p hp alpha halpha Q u hu e) ∧
    (∫ J, intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J
      ∂pureLaw p hp alpha halpha Q u hu e) =
      c * (∫ J, intrinsicDet μ Q u J *
        quadraticBankPartition μ a β u J
        ∂pureLaw p hp alpha halpha Q u hu e) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let ρ := sphereLaw (d+1)
  let D := intrinsicDet μ Q u
  let F := originalLatitudeBankPoint μ a β u
  let G := quadraticBankPoint μ a β u
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν,pureLaw]
    infer_instance
  have hDmeas : Measurable D := by
    unfold D intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hD0 (J : Disorder (d+2) μ.maxDegree) : 0 ≤ D J := abs_nonneg _
  have hGjoint : Measurable (fun w : Disorder (d+2) μ.maxDegree × Vector (d+1) =>
      D w.1 * G w.1 w.2) :=
    (hDmeas.comp measurable_fst).mul
      (quadraticBankPoint_joint_measurable μ a β u)
  have hswap : Measurable (fun w : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      (w.2,w.1)) := measurable_snd.prodMk measurable_fst
  have hFm : Measurable (fun w : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      F w.2 w.1) := by
    simpa only [F,Function.comp_def,Prod.fst,Prod.snd] using
      (originalLatitudeBankPoint_joint_measurable μ a β u).comp hswap
  have hFjoint : Measurable (fun w : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      D w.2 * F w.2 w.1) := (hDmeas.comp measurable_snd).mul hFm
  have hpoint : ∀ᵐ y ∂ρ,
      (∫ J, D J * F J y ∂ν) = c*(∫ J, D J * G J y ∂ν) := by
    filter_upwards [sphereLaw_support (by omega : 1 ≤ d+1)] with y hy
    have hh := pure_palm_determinant_latitude_factorization
      p hp alpha halpha hμ hQ a β ha u
      (quadraticBankDirection (d+1) u y)
      hu (quadraticBankDirection_tangent u hu y) e
    dsimp only at hh
    rw [← pureLaw_eq_valueConditionedLaw p hp alpha halpha Q u hu e] at hh
    rw [hres y hy] at hh
    simpa only [D,F,G,originalLatitudeBankPoint,quadraticBankPoint] using hh
  exact PositiveAngularFactorization.weighted_integral_factorization
    ν ρ D F G c hD0
    (fun J y => (Real.exp_pos _).le)
    (fun J y => (Real.exp_pos _).le)
    hGjoint hFjoint
    (fun J => quadraticBankPoint_integrable_direction μ a β u J)
    hpointInt hpoint hbankInt

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
