-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapScaledFourPiece
public import SlowEquilibration.SphericalPureLaplaceUniformLogPhysicalCurvature
public import SlowEquilibration.SphericalPureCapExteriorFixedScaled

@[expose] public section

/-! Source §9.19: the whole proper-pure cap has the contact Gaussian
asymptotic after its exact logarithmic critical-value centering. -/

namespace SlowEquilibration.SphericalPureCapFullLaplaceFixedPointwise
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapSourceScalars SphericalPureCapTailScale
open SphericalPureCapExteriorFixedScaled
open SphericalPureCapIntegralDecomposition
open SphericalPureCapCenteredEnergyBounds SphericalPureCapScaledFourPiece
open SphericalPureCapCenteringIdentity
open SphericalPureLaplaceUniformLogPhysicalCurvature
open SphericalPureLaplaceUniformLogCurvature PureStationarity
open SphericalModel
open scoped Topology
set_option autoImplicit false

private theorem dim_sub_one (n : ℕ) : n+2-1=n+1 := by omega

/-- The full raw cap integral converges to the source Gaussian contact
constant for every shift in one fixed energy window. The cap and contact
band obey the two source strict margins and use the exact printed curvature. -/
theorem sourcePure_cap_full_laplace_fixed_pointwise
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    let F := CSParisiMeasure.variationalValue μ β
    ∃ a b ε κ : ℝ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ q+b < 1-ε ∧
      0 < ε ∧ ε < 1 ∧ 0 < κ ∧
      κ = purePrintedKStar p hp β Q ∧
      pureResidualCoefficient p β a < 1/2 ∧
      cp < β*a^p ∧
      ∀ L : ℝ, 0 ≤ L → ∀ t ∈ Icc (-L) L,
        Tendsto (fun n : ℕ =>
          capScale (n+2) F (1/(2*x)) *
            ((latitudeNormalization (n+1)).toReal *
              (∫ z in a..1,
                rawDensity p (n+2) β
                  ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z)))
          atTop
          (𝓝 (((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
            Real.exp (β*t*q^p) * Real.sqrt (Real.pi/(κ/2)))) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let F := CSParisiMeasure.variationalValue μ β
  let φ := sourcePureLatitudeExponent p 1 Q β (markE μ β x Q)
  obtain ⟨b₀,κ,hb₀,hb₀q,hb₀r,hκ,hκEq,hlocal⟩ :=
    sourcePureLatitude_uniform_log_physical_exact_curvature p hp h
  obtain ⟨a,b,ε,haHalf,hab,hb,hbb₀,hqε,hε0,hε1,hCa,hDepth,
    hcontact,hTails⟩ :=
    sourcePure_cap_exterior_fixed_scaled_vanishes p hp h hb₀ hb₀r
  refine ⟨a,b,ε,κ,haHalf,hab,hb,hqε,hε0,hε1,hκ,hκEq,hCa,hDepth,?_⟩
  intro L hL t ht
  obtain ⟨hLeft,hRight,hPole⟩ := hTails L hL
  let uN : ℕ → ℝ := fun N => t-Real.log (N:ℝ)/(2*cp)
  let HN : ℕ → ℝ := fun N => (N:ℝ)*ep+uN N
  have hcp : 0 < cp := pureIntensityConstant_pos p (by omega)
  have hu : ∀ᶠ N : ℕ in atTop, uN N ≤ L := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
    have hshift : 0 ≤ Real.log (N:ℝ)/(2*cp) :=
      div_nonneg hlog (by positivity)
    dsimp [uN]
    linarith [ht.2]
  have hH : ∀ᶠ N : ℕ in atTop,
      0 ≤ HN N ∧ HN N ≤ (N:ℝ)*ep+L := by
    filter_upwards [sourcePure_centered_energy_eventually_in_pole_window
      p hp h L] with N hN
    have hh := hN.2 t ht
    simpa only [HN,uN,ep,cp,add_sub_assoc] using hh
  have hLeftN := hLeft uN hu
  have hRightN := hRight uN hu
  have hPoleN := hPole HN hH
  have hLeftn : Tendsto (fun n : ℕ =>
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in a..q-b, profileDensity p (n+2) (by omega) Q β x
            (uN (n+2)) z))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,profileDensity,dim_sub_one,μ,q,φ,F] using
      hLeftN.comp (tendsto_add_atTop_nat 2)
  have hRightn : Tendsto (fun n : ℕ =>
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in q+b..1-ε, profileDensity p (n+2) (by omega) Q β x
            (uN (n+2)) z))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,profileDensity,dim_sub_one,μ,q,φ,F] using
      hRightN.comp (tendsto_add_atTop_nat 2)
  have hPolen : Tendsto (fun n : ℕ =>
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in 1-ε..1, rawDensity p (n+2) β (HN (n+2)) z)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,dim_sub_one,μ,F] using
      hPoleN.comp (tendsto_add_atTop_nat 2)
  have hLocaln : Tendsto (fun n : ℕ =>
      (latitudeNormalization (n+1)).toReal *
        (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
          Real.exp ((n+2 : ℕ)*(φ z-φ q)+β*t*q^p+
            β*(uN (n+2))*(z^p-q^p)))) atTop
      (𝓝 (((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
        Real.exp (β*t*q^p) * Real.sqrt (Real.pi/(κ/2)))) := by
    simpa only [uN,μ,q,φ,cp] using
      ((hlocal b hb hbb₀ L).1.tendsto_at ht)
  have hSum := (((hLeftn.add hLocaln).add hRightn).add hPolen)
  have hEq : ∀ᶠ n : ℕ in atTop,
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in a..1, rawDensity p (n+2) β (HN (n+2)) z)) =
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in a..q-b, profileDensity p (n+2) (by omega) Q β x
            (uN (n+2)) z)) +
      (latitudeNormalization (n+1)).toReal *
        (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
          Real.exp ((n+2 : ℕ)*(φ z-φ q)+β*t*q^p+
            β*(uN (n+2))*(z^p-q^p))) +
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in q+b..1-ε, profileDensity p (n+2) (by omega) Q β x
            (uN (n+2)) z)) +
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in 1-ε..1, rawDensity p (n+2) β (HN (n+2)) z)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hdim : 4 ≤ n+2 := by omega
    have hgeom : 0 < a := lt_trans (by positivity : 0 < 1/Real.sqrt 2) haHalf
    have hsplit := sourcePure_scaled_cap_four_piece p hp h (n+2) hdim t a b ε
      hgeom hab.le hb.le hqε.le hε0
    simpa only [dim_sub_one,μ,q,φ,cp,ep,F,uN,HN,add_sub_assoc]
      using hsplit
  have hFinal := hSum.congr' (hEq.mono fun _ hn => hn.symm)
  simpa only [zero_add,add_zero,μ,q,cp,ep,F,HN,uN,add_sub_assoc]
    using hFinal

end
end SlowEquilibration.SphericalPureCapFullLaplaceFixedPointwise
