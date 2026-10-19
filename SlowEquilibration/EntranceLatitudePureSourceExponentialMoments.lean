-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceExponentialMoments
public import SlowEquilibration.EntranceLatitudePureSourceCorrectionBound
public import SlowEquilibration.ConditionedEntrancePureJointHamiltonian

/-! Genuine proper-pure source latitude exponential and weighted moments,
from the actual homogeneous value-plus-zero-gradient correction. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance SphericalTwoPointCovariance
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Proper pure source correction is jointly polynomial, hence continuous
in the actual frozen axis. -/
theorem pureSourceRegressionCorrection_axis_continuous {N : ℕ}
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (e : ℝ) (x : Vector N) :
    Continuous (fun u => pureSourceRegressionCorrection p hp c hc Q J u e x) := by
  exact (attachedPureCorrection_jointContDiff (FiniteMixture.pure p hp c hc) p Q).continuous.comp
    (show Continuous (fun u : Vector N => ((J,(u,(e,(0 : ℝ)))),x)) by fun_prop)

private theorem pure_source_delta_latitude_bound {n : ℕ} (hn : 1≤n)
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) {Q : ℝ} (hQ : 0<Q) {M : ℝ} (hM : 0≤M)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree) (hJ : J∈regularDisorder)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {e r : ℝ} (he : |e|≤M)
    (hr : |r|≤1) :
    let μ := FiniteMixture.pure p hp c hc
    ∀ᵐ u ∂latitudeLaw x (latitudeFrameAt x) r,
      |pureSourceRegressionCorrection p hp c hc Q J u e x|≤
      sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|) := by
  dsimp only
  filter_upwards [latitudeLaw_support hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) hr] with u hu
  have h := actual_pureSourceRegressionCorrection_abs_le_observable p hp c hc hQ hM J hJ u x hu.1 hx he
  rw [overlap_comm u x,hu.2] at h
  exact h

/-- Actual proper pure δ has a genuine latitude exponential moment. -/
theorem actual_pureSourceRegressionCorrection_latitude_exp_abs_le {n : ℕ} (hn : 1≤n)
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) {Q : ℝ} (hQ : 0<Q)
    {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J∈originalLatitudeMeanGood n (FiniteMixture.pure p hp c hc))
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {e r : ℝ} (he : |e|≤M)
    (hr : r∈Ioo (-1 : ℝ) 1) :
    let μ := FiniteMixture.pure p hp c hc
    Integrable (fun u => Real.exp (ζ*|pureSourceRegressionCorrection p hp c hc Q J u e x|))
      (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,Real.exp (ζ*|pureSourceRegressionCorrection p hp c hc Q J u e x|) ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeMomentConstant μ Q M ζ*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  exact latitude_source_dominated_exp_abs_le hn _ hQ.le hM hζ J hJ x hx hr _
    (pureSourceRegressionCorrection_axis_continuous p hp c hc Q J e x)
    (pure_source_delta_latitude_bound hn p hp c hc hQ hM J hJ.1 x hx he (abs_lt.mpr hr).le)

/-- Actual proper pure δ and its sampled H_Q tangent square have a genuine
latitude weighted second moment with the literal radial order. -/
theorem actual_pureSourceRegressionCorrection_latitude_observable_square_exp_abs_le {n : ℕ} (hn : 1≤n)
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) {Q : ℝ} (hQ : 0<Q)
    {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J∈originalLatitudeMeanGood n (FiniteMixture.pure p hp c hc))
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {e r : ℝ} (he : |e|≤M)
    (hr : r∈Ioo (-1 : ℝ) 1) :
    let μ := FiniteMixture.pure p hp c hc
    let cQ := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (fun u => (observable cQ J x u)^2*Real.exp (ζ*|pureSourceRegressionCorrection p hp c hc Q J u e x|))
      (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,(observable cQ J x u)^2*Real.exp (ζ*|pureSourceRegressionCorrection p hp c hc Q J u e x|)
      ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeMomentConstant μ Q M ζ*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2))*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  exact latitude_source_dominated_observable_square_exp_abs_le hn _ hQ.le hM hζ J hJ x hx hr _
    (pureSourceRegressionCorrection_axis_continuous p hp c hc Q J e x)
    (pure_source_delta_latitude_bound hn p hp c hc hQ hM J hJ.1 x hx he (abs_lt.mpr hr).le)

end
end SlowEquilibration.EntranceLatitudeTangentObservable
