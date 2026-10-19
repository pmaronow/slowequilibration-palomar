-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalReplicaMagnetization
public import SlowEquilibration.SphericalBarycenterGoodSet

/-!
# Literal constructed-observable projection and stationary plateau

The observable is selected internally as the source overlap-weighted Gibbs
barycenter. The inputs are the actual restricted-partition good-reference
event and actual replica mass. Their stochastic failure probabilities remain
separate pressure obligations; no aligned low-energy observable is assumed.
-/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalSourceObservablePlateau

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalBarycenter SphericalPhysicalSpectral
open SphericalLaplaceIdentification SphericalCenteredObservables SphericalSpinProjection
open SphericalSpinCorrelation SphericalReplicaMagnetization
open scoped Topology InnerProductSpace NNReal ENNReal

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def plateauTime (τ : ℝ) (N : ℕ) : ℝ≥0 := ⟨Real.exp (τ * N), (Real.exp_pos _).le⟩

private lemma exp_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.exp (-a * N)) atTop (𝓝 (0 : ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply, neg_mul]

private lemma errors_eventually (q₁ ε b a r C cE σ τ : ℝ)
    (ha : 0 < a) (hr : 0 < r) (hσ : σ < cE) (hτ : τ < cE)
    (hmargin : Real.sqrt b + Real.sqrt ε < q₁) :
    ∀ᶠ N : ℕ in atTop,
      Real.sqrt b + Real.sqrt ε + (1+q₁)*(Real.exp (-(N : ℝ)) + Real.exp (-a * N)) +
        Real.exp (-(r/2) * N) + Real.sqrt (C * Real.exp (-(cE-σ) * N)) ≤ q₁ ∧
      Real.sqrt b + Real.sqrt ε + (1+q₁)*(Real.exp (-(N : ℝ)) + Real.exp (-a * N)) +
        Real.exp (-(r/2) * N) + Real.sqrt ((C/2) * Real.exp (-(cE-τ) * N)) ≤ q₁ := by
  have h1 : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_one_mul] using exp_decay (show (0 : ℝ) < 1 by norm_num)
  have hbase := ((h1.add (exp_decay ha)).const_mul (1+q₁)).add (exp_decay (half_pos hr))
  have hp := hbase.add (((exp_decay (sub_pos.mpr hσ)).const_mul C).sqrt)
  have ht := hbase.add (((exp_decay (sub_pos.mpr hτ)).const_mul (C/2)).sqrt)
  simp only [add_zero, mul_zero, Real.sqrt_zero] at hp ht
  have hm : 0 < q₁ - Real.sqrt b - Real.sqrt ε := by linarith
  filter_upwards [hp.eventually (gt_mem_nhds hm), ht.eventually (gt_mem_nhds hm)] with N hP hT
  constructor <;> linarith

/-- Both the low-mode centered-spin mass and the genuine stationary
connected-overlap plateau follow from actual model events. The projection
and time exponents may independently approach the proved energy exponent.
Constants are chosen before dimension, mixture, field and disorder. -/
theorem constructed_plateau_eventually (J G δ q₁ q₂ a ε b r : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hgap : 4*δ < G) (ha : 0 < a)
    (hq₁ : 0 < q₁) (hq : q₁ < q₂) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hr : 0 < r)
    (hmargin : Real.sqrt b + Real.sqrt ε < q₁) :
    ∃ C cE : ℝ, 0 < C ∧ 0 < cE ∧ cE = min (G-4*δ) a / 2 ∧
      ∀ σ τ : ℝ, σ < cE → τ < cE →
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 2 ≤ N) (μ : FiniteMixture) (β F q w : ℝ)
        (D : Disorder N μ.maxDegree), q₂ ≤ q-w →
        D ∈ goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a * N)) →
        ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real (replicaOverlapEvent ε) ≤ Real.exp (-r * N) →
        b ≤ ‖vectorCutoff hN μ D β (Real.exp (-σ * N))
          (centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp)))‖^2 ∧
        ∀ t ≤ plateauTime τ N, b ≤ connectedSpinCorrelation μ D β t := by
  obtain ⟨C,cE,hC,hcE,hcEq,hConstruction⟩ :=
    sourceObservable_on_goodReference_event_eventually J G δ q₁ q₂ a 0
      hJ hδ hgap ha hq₁ hq hq₁
  refine ⟨C,cE,hC,hcE,hcEq,?_⟩
  intro σ τ hσ hτ
  filter_upwards [hConstruction, errors_eventually q₁ ε b a r C cE σ τ ha hr hσ hτ hmargin]
    with N hConstruct hErrors
  intro hN μ β F q w D hcore hD hrep
  have hN1 : 1 ≤ N := by omega
  have hResult := hConstruct μ.maxDegree (mixtureCoefficients μ) β F q w D hcore hD
  obtain ⟨_hS,_hSphere,_hBad,hBs,hB,hEnergy,_hAlign,hMean⟩ := hResult
  let B := sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂
  have hBs' : ContDiff ℝ 1 B := hBs.of_le (by simp)
  have hB' : ∀ x, SphericalAging.HardSphereDynamics.OnSphere x → ‖B x‖ ≤ 1 := fun x _ => hB x
  have hEnergy' : vectorDirichletEnergy β (potential μ D) B ≤ C * Real.exp (-cE * N) := hEnergy
  have hMean' : q₁-(1+q₁)*(Real.exp (-(N : ℝ))+Real.exp (-a * N)) ≤
      ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β D := hMean
  have hMag := mixture_magnetization_le_of_replica hN1 μ D β hε hrep
  have hProjEnergy : vectorDirichletEnergy β (potential μ D) B / Real.exp (-σ * N) ≤
      C * Real.exp (-(cE-σ) * N) := by
    have hh := div_le_div_of_nonneg_right hEnergy' (Real.exp_pos (-σ * N)).le
    apply hh.trans_eq
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  have hProjSqrt := Real.sqrt_le_sqrt hProjEnergy
  have hTimeEnergy : (plateauTime τ N : ℝ) * vectorDirichletEnergy β (potential μ D) B / 2 ≤
      (C/2) * Real.exp (-(cE-τ) * N) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEnergy' (Real.exp_pos (τ * N)).le) (show (0 : ℝ) ≤ 2 by norm_num)
    apply hh.trans_eq
    change Real.exp (τ * N) * (C * Real.exp (-cE * N)) / 2 = _
    calc
      _ = (C/2) * (Real.exp (τ * N) * Real.exp (-cE * N)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hTimeSqrt := Real.sqrt_le_sqrt hTimeEnergy
  have hPmargin : Real.sqrt b ≤ q₁-(1+q₁)*(Real.exp (-(N : ℝ))+Real.exp (-a * N)) -
      ‖mean μ D β spin‖ - Real.sqrt (vectorDirichletEnergy β (potential μ D) B / Real.exp (-σ * N)) := by
    linarith [hErrors.1]
  have hTmargin : Real.sqrt b ≤ q₁-(1+q₁)*(Real.exp (-(N : ℝ))+Real.exp (-a * N)) -
      ‖mean μ D β spin‖ - Real.sqrt ((plateauTime τ N : ℝ) * vectorDirichletEnergy β (potential μ D) B / 2) := by
    linarith [hErrors.2]
  constructor
  · have hproj := spin_projection_norm_lower hN μ D β B hBs' hB' (Real.exp_pos (-σ * N)) hMean'
    have hbound := hPmargin.trans (le_max_right 0 _ |>.trans hproj)
    have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg b) hbound 2
    rw [Real.sq_sqrt hb] at hsquare
    exact hsquare
  · intro t ht
    have hcor := direct_connected_correlation_uniform hN μ D β B hBs' hB' hMean' (plateauTime τ N) t ht
    have hmax := hTmargin.trans (le_max_right 0 _)
    have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg b) hmax 2
    rw [Real.sq_sqrt hb] at hsquare
    exact hsquare.trans hcor

end SlowEquilibration.SphericalSourceObservablePlateau
