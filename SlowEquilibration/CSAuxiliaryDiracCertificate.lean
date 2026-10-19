-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureElasticity
public import SlowEquilibration.CSLatitudeEntropyCalculus
public import SlowEquilibration.CSConvexity

@[expose] public section

/-!
# Actual auxiliary latitude Dirac minimizer certificate

The ordinary auxiliary covariance and actual Dirac law are used throughout.
The first-variation maximum is derived from genuine mixture elasticity and
the genuine strict-superlevel endpoint; optimality is a conclusion.
-/

namespace SlowEquilibration.CSAuxiliaryDiracCertificate

noncomputable section
open Set MeasureTheory
open CrisantiSommers
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem latitudeDirac_affine {q : ℝ} (hq : 0 ≤ q) :
    q^2+(1-q^2)*latitudeDiracLocation q = q := by
  unfold latitudeDiracLocation
  field_simp [show 1+q ≠ 0 by linarith]
  ring

theorem latitudeDirac_one_sub {q : ℝ} (hq : 0 ≤ q) :
    1-latitudeDiracLocation q = 1/(1+q) := by
  unfold latitudeDiracLocation
  field_simp [show 1+q ≠ 0 by linarith]
  ring

theorem latitudeSlope_hasDerivAt (μ : FiniteMixture) (q : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun r : ℝ => μ.xi1 (q^2+(1-q^2)*r)/r)
      (((1-q^2)*μ.xi2 (q^2+(1-q^2)*s)*s-μ.xi1 (q^2+(1-q^2)*s))/s^2) s := by
  have hlin := ((hasDerivAt_id s).const_mul (1-q^2)).const_add (q^2)
  have h := ((μ.hasDerivAt_xi1 (q^2+(1-q^2)*s)).comp s hlin).div (hasDerivAt_id s) hs
  convert h using 1
  · ext r
    rfl
  · dsimp only [id_eq, Pi.mul_apply, Function.comp_apply]
    ring

/-- The true elasticity bound forces the actual first-variation slope
ratio to decrease before the Dirac atom. -/
theorem latitudeSlope_antitoneOn (μ : FiniteMixture) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (he : μ.elasticity q ≤ 1/(1-q)) :
    AntitoneOn (fun s : ℝ => μ.xi1 (q^2+(1-q^2)*s)/s)
      (Ioc (0 : ℝ) (latitudeDiracLocation q)) := by
  have ha := latitudeDiracLocation_mem ⟨hq.1.le, hq.2⟩
  have hc : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (latitudeDiracLocation q))
  · intro s hs
    exact (latitudeSlope_hasDerivAt μ q hs.1.ne').continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) (latitudeDiracLocation q) := by
      simpa only [interior_Ioc] using hs
    exact (latitudeSlope_hasDerivAt μ q hs'.1.ne').differentiableAt.differentiableWithinAt
  · intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) (latitudeDiracLocation q) := by
      simpa only [interior_Ioc] using hs
    let u := q^2+(1-q^2)*s
    have hu0 : 0 < u := by
      have hmul := mul_nonneg hc hs'.1.le
      dsimp [u]
      nlinarith [sq_pos_of_pos hq.1]
    have huq : u ≤ q := by
      have hmul := mul_le_mul_of_nonneg_left hs'.2.le hc
      rw [← latitudeDirac_affine hq.1.le]
      dsimp [u]
      linarith
    have hue : μ.elasticity u ≤ 1/(1-q) :=
      (μ.elasticity_monotoneOn hu0 hq.1 huq).trans he
    change u*μ.xi2 u/μ.xi1 u ≤ 1/(1-q) at hue
    have hscaled := (div_le_div_iff₀ (μ.xi1_pos hu0) (sub_pos.mpr hq.2)).mp hue
    have hqu := mul_le_mul_of_nonneg_left huq hq.1.le
    have hcr : (1-q^2)*s ≤ u*(1-q) := by
      calc
        (1-q^2)*s = u-q^2 := by dsimp [u]; ring
        _ ≤ u-q*u := by simpa only [pow_two] using sub_le_sub_left hqu u
        _ = u*(1-q) := by ring
    have hprod := mul_le_mul_of_nonneg_right hcr (μ.xi2_pos hu0).le
    rw [(latitudeSlope_hasDerivAt μ q hs'.1.ne').deriv]
    apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [hprod, hscaled]) (sq_nonneg s)

theorem plateau_auxiliary_atom_equation (μ : FiniteMixture) {q β : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hplateau : β^2*μ.xi1 q = q/(1-q)) :
    β^2*(1-q^2)*μ.xi1 q =
      latitudeDiracLocation q/(1-latitudeDiracLocation q)^2 := by
  calc
    _ = (1-q^2)*(β^2*μ.xi1 q) := by ring
    _ = (1-q^2)*(q/(1-q)) := by rw [hplateau]
    _ = _ := by
      rw [latitudeDirac_one_sub hq.1.le]
      unfold latitudeDiracLocation
      field_simp [(sub_pos.mpr hq.2).ne', show 1+q ≠ 0 by linarith [hq.1]]
      ring

/-- Genuine nonnegative auxiliary first-variation derivative below the
atom, deduced from actual finite-mixture elasticity and the plateau equation. -/
theorem firstVariation_deriv_nonneg_before_atom (μ : FiniteMixture) {q β s : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (he : μ.elasticity q ≤ 1/(1-q))
    (hplateau : β^2*μ.xi1 q = q/(1-q))
    (hs : s ∈ Icc (0 : ℝ) (latitudeDiracLocation q)) :
    0 ≤ deriv (firstVariation β (μ.auxiliaryCovariance q)
      (Measure.dirac (latitudeDiracLocation q))) s := by
  have ha := latitudeDiracLocation_mem ⟨hq.1.le, hq.2⟩
  have ha0 : 0 < latitudeDiracLocation q := div_pos hq.1 (by linarith [hq.1])
  have hc : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  rw [firstVariation_auxiliary_dirac_deriv_of_le μ β ⟨hq.1.le, hq.2⟩
    ⟨hs.1, hs.2.trans_lt ha.2⟩ hs.2]
  by_cases hs0 : s = 0
  · subst s
    simp only [mul_zero, add_zero, zero_div, sub_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg β) hc) (μ.xi1_nonneg (sq_nonneg q))
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hm := latitudeSlope_antitoneOn μ hq he
      ⟨hspos, hs.2⟩ ⟨ha0, le_rfl⟩ hs.2
    dsimp only at hm
    rw [latitudeDirac_affine hq.1.le] at hm
    have hbound := mul_le_mul_of_nonneg_right hm
      (mul_nonneg (mul_nonneg (sq_nonneg β) hc) hspos.le)
    have hleft : (μ.xi1 q/latitudeDiracLocation q)*(β^2*(1-q^2)*s) =
        s/(1-latitudeDiracLocation q)^2 := by
      calc
        _ = (β^2*(1-q^2)*μ.xi1 q)*s/latitudeDiracLocation q := by ring
        _ = _ := by
          rw [plateau_auxiliary_atom_equation μ hq hplateau]
          field_simp [ha0.ne']
    have hright : (μ.xi1 (q^2+(1-q^2)*s)/s)*(β^2*(1-q^2)*s) =
        β^2*(1-q^2)*μ.xi1 (q^2+(1-q^2)*s) := by field_simp [hs0]
    rw [hleft, hright] at hbound
    linarith

/-- The actual auxiliary entropy derivative above the Dirac atom equals
the literal overlap expression that appears in the plateau inequality. -/
theorem latitude_entropy_above_atom {q s : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : s < 1) :
    latitudeDiracLocation q/(1-latitudeDiracLocation q)^2+
      (1-s)⁻¹-(1-latitudeDiracLocation q)⁻¹ =
        (1-q^2)*((q^2+(1-q^2)*s)/(1-(q^2+(1-q^2)*s))) := by
  let a := latitudeDiracLocation q
  let c := 1-q^2
  let u := q^2+c*s
  have hc : 0 < c := by dsimp [c]; nlinarith [hq.1, hq.2]
  have hsden : 1-s ≠ 0 := (sub_pos.mpr hs).ne'
  have hprefix : a/(1-a)^2-(1-a)⁻¹ = -c := by
    rw [show 1-a = 1/(1+q) from latitudeDirac_one_sub hq.1.le]
    dsimp [a, c, latitudeDiracLocation]
    field_simp [show 1+q ≠ 0 by linarith [hq.1]]
    ring
  have hdenu : 1-u = c*(1-s) := by dsimp [u, c]; ring
  have huEq : u = 1-c*(1-s) := by dsimp [u, c]; ring
  change a/(1-a)^2+(1-s)⁻¹-(1-a)⁻¹ = c*(u/(1-u))
  calc
    _ = (1-s)⁻¹-c := by linarith
    _ = _ := by
      rw [hdenu, huEq]
      field_simp [hc.ne', hsden]

/-- The actual right-hand dynamical tail makes the genuine auxiliary
first-variation derivative nonpositive above its atom. -/
theorem firstVariation_deriv_nonpos_after_atom (μ : FiniteMixture) {β s : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (hs : s ∈ Ico (0 : ℝ) 1)
    (has : latitudeDiracLocation (Thresholds.qStar μ.xi β) ≤ s) :
    deriv (firstVariation β (μ.auxiliaryCovariance (Thresholds.qStar μ.xi β))
      (Measure.dirac (latitudeDiracLocation (Thresholds.qStar μ.xi β)))) s ≤ 0 := by
  let q := Thresholds.qStar μ.xi β
  let u := q^2+(1-q^2)*s
  have hq : q ∈ Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hc : 0 < 1-q^2 := by nlinarith [hq.1, hq.2]
  have huq : q ≤ u := by
    have h := mul_le_mul_of_nonneg_left has hc.le
    rw [← latitudeDirac_affine hq.1.le]
    dsimp [u]
    linarith
  have hu : u ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨hq.1.trans_le huq, ?_⟩
    have h := mul_lt_mul_of_pos_left hs.2 hc
    dsimp [u]
    nlinarith
  have hlevel : β^2*Thresholds.A μ.xi q = 1 :=
    (Thresholds.plateau_iff hq).mpr (μ.qStar_solves_plateau hβ).2
  have htail : β^2*Thresholds.A μ.xi u ≤ 1 := by
    by_cases heq : u = q
    · simpa only [heq] using hlevel.le
    · exact μ.A_le_one_of_qStar_lt (β := β) hu (lt_of_le_of_ne huq (Ne.symm heq))
  unfold Thresholds.A at htail
  rw [(μ.hasDerivAt_xi u).deriv, ← mul_div_assoc] at htail
  have hscaled := (div_le_iff₀ hu.1).mp htail
  have hbound : β^2*μ.xi1 u ≤ u/(1-u) := by
    apply (le_div_iff₀ (sub_pos.mpr hu.2)).mpr
    nlinarith
  rw [firstVariation_auxiliary_dirac_deriv_of_ge μ β ⟨hq.1.le, hq.2⟩ hs has,
    latitude_entropy_above_atom hq hs.2]
  have hmul := mul_le_mul_of_nonneg_left hbound hc.le
  change β^2*(1-q^2)*μ.xi1 u-(1-q^2)*(u/(1-u)) ≤ 0
  nlinarith

/-- At the genuine plateau, the actual auxiliary first variation has a
global maximum at the literal one-atom trial overlap. -/
theorem firstVariation_maximum_at_latitudeDirac (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    let q := Thresholds.qStar μ.xi β
    ∀ s ∈ Ico (0 : ℝ) 1,
      firstVariation β (μ.auxiliaryCovariance q) (Measure.dirac (latitudeDiracLocation q)) s ≤
        firstVariation β (μ.auxiliaryCovariance q) (Measure.dirac (latitudeDiracLocation q))
          (latitudeDiracLocation q) := by
  let q := Thresholds.qStar μ.xi β
  let a := latitudeDiracLocation q
  let f := firstVariation β (μ.auxiliaryCovariance q) (Measure.dirac a)
  change ∀ s ∈ Ico (0 : ℝ) 1, f s ≤ f a
  have hq : q ∈ Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have ha : a ∈ Ico (0 : ℝ) 1 := latitudeDiracLocation_mem ⟨hq.1.le, hq.2⟩
  have hcut : HasCutoff (Measure.dirac a) a := dirac_hasCutoff ha
  have hdiff (s : ℝ) (hs : s < 1) : DifferentiableAt ℝ f s :=
    (firstVariation_hasDerivAt β (μ.auxiliaryCovariance q) (Measure.dirac a)
      hcut hs (μ.auxiliaryCovariance_hasDerivAt q s)).differentiableAt
  have hplateau : β^2*μ.xi1 q = q/(1-q) := by
    have h := (μ.qStar_solves_plateau hβ).2
    rwa [(μ.hasDerivAt_xi q).deriv] at h
  have he : μ.elasticity q ≤ 1/(1-q) := μ.elasticity_qStar_le hβ
  have hmono : MonotoneOn f (Icc (0 : ℝ) a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
    · intro s hs
      exact (hdiff s (hs.2.trans_lt ha.2)).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) a := by simpa only [interior_Icc] using hs
      exact (hdiff s (hs'.2.trans ha.2)).differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) a := by simpa only [interior_Icc] using hs
      exact firstVariation_deriv_nonneg_before_atom μ hq he hplateau ⟨hs'.1.le, hs'.2.le⟩
  have hanti : AntitoneOn f (Ico a 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico a 1)
    · intro s hs
      exact (hdiff s hs.2).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo a 1 := by simpa only [interior_Ico] using hs
      exact (hdiff s hs'.2).differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo a 1 := by simpa only [interior_Ico] using hs
      exact firstVariation_deriv_nonpos_after_atom μ hβ ⟨ha.1.trans hs'.1.le, hs'.2⟩ hs'.1.le
  intro s hs
  by_cases hsa : s ≤ a
  · exact hmono ⟨hs.1, hsa⟩ ⟨ha.1, le_rfl⟩ hsa
  · have has : a ≤ s := (lt_of_not_ge hsa).le
    exact hanti ⟨le_rfl, ha.2⟩ ⟨has, hs.2⟩ has

/-- Proposition pr-certificate(b): the actual auxiliary latitude Dirac law
is a global minimizer of the ordinary CS functional over every admissible
probability law. No optimality or replica-symmetry premise is assumed. -/
theorem latitudeDiracCandidate_isMinimizer (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    let q := Thresholds.qStar μ.xi β
    (latitudeDiracCandidate q ⟨(μ.qStar_solves_plateau hβ).1.1.le,
      (μ.qStar_solves_plateau hβ).1.2⟩).IsMinimizer β (μ.auxiliaryCovariance q) := by
  let q := Thresholds.qStar μ.xi β
  have hq : q ∈ Ico (0 : ℝ) 1 :=
    ⟨(μ.qStar_solves_plateau hβ).1.1.le, (μ.qStar_solves_plateau hβ).1.2⟩
  let ζ := latitudeDiracCandidate q hq
  apply ζ.minimizer_of_support_on_maximum β (μ.auxiliaryCovariance q)
    (μ.auxiliaryCovariance_continuous q).continuousOn
    (firstVariation β (μ.auxiliaryCovariance q) ζ.law (latitudeDiracLocation q))
  · exact firstVariation_maximum_at_latitudeDirac μ hβ
  · change ∀ᵐ s ∂Measure.dirac (latitudeDiracLocation q),
      firstVariation β (μ.auxiliaryCovariance q) ζ.law s =
        firstVariation β (μ.auxiliaryCovariance q) ζ.law (latitudeDiracLocation q)
    simp

/-- Literal global CS lower bound at the actual auxiliary covariance: every
ordinary probability law compactly supported below one has value at least
the evaluated physical latitude trial. -/
theorem latitudePressureTrial_le_functional (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {r : ℝ} (hν : HasCutoff ν r) :
    let q := Thresholds.qStar μ.xi β
    SphericalModel.latitudePressureTrial μ β q ≤
      functional β (μ.auxiliaryCovariance q) ν r := by
  let q := Thresholds.qStar μ.xi β
  have hq : q ∈ Ico (0 : ℝ) 1 :=
    ⟨(μ.qStar_solves_plateau hβ).1.1.le, (μ.qStar_solves_plateau hβ).1.2⟩
  let ζ := latitudeDiracCandidate q hq
  let νA : Admissible := ⟨ν, inferInstance, ⟨r, hν⟩⟩
  have hmin : ζ.IsMinimizer β (μ.auxiliaryCovariance q) :=
    latitudeDiracCandidate_isMinimizer μ hβ
  have hbound := hmin νA
  rw [show ζ.value β (μ.auxiliaryCovariance q) =
    SphericalModel.latitudePressureTrial μ β q from latitudeDiracCandidate_value μ β hq,
    νA.value_eq β _ hν] at hbound
  exact hbound

/-- The actual auxiliary global minimizer is unique as an ordinary law,
using the proved strict CS convexity, rather than a uniqueness premise. -/
theorem latitudeDirac_minimizer_law_unique (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (ν : Admissible)
    (hν : ν.IsMinimizer β (μ.auxiliaryCovariance (Thresholds.qStar μ.xi β))) :
    ν.law = Measure.dirac (latitudeDiracLocation (Thresholds.qStar μ.xi β)) := by
  let q := Thresholds.qStar μ.xi β
  have hq : q ∈ Ico (0 : ℝ) 1 :=
    ⟨(μ.qStar_solves_plateau hβ).1.1.le, (μ.qStar_solves_plateau hβ).1.2⟩
  let ζ := latitudeDiracCandidate q hq
  exact ν.minimizer_law_unique ζ β (μ.auxiliaryCovariance q)
    (μ.auxiliaryCovariance_continuous q).continuousOn hν
    (latitudeDiracCandidate_isMinimizer μ hβ)

end

end SlowEquilibration.CSAuxiliaryDiracCertificate
