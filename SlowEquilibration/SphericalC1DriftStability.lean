-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PicardDriftStability
public import SlowEquilibration.SphericalC1Dynamics
public import SphericalAging.TerminalStateRepresentation
public import SphericalAging.ActualSphereFeller

/-! Actual sphere-valued Brownian solutions depend continuously on their
drift restricted to the sphere. No common ambient Lipschitz constant for
the approximating gradients is required. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalC1Dynamics
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalModel SphericalDynamics PredictableItoTime PredictableDriftTime
open PicardDependence PicardDriftStability TerminalStateRepresentation TerminalLinearity
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {N : ℕ}

/-- The actual finite-horizon predictable class of the canonical C¹ process. -/
def stateClass (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (T : ℝ≥0) :=
  GlobalSDE.horizonClass (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x T

theorem stateClass_onSphere (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod (VectorBrownian.law N),q.1∈Ioc 0 T →
      OnSphere ((stateClass β g hg x T : Lp (State N) 2
        (nonnegativeLebesgueMeasure.prod (VectorBrownian.law N))) q) := by
  have hp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure)
    (ν := VectorBrownian.law N)).ae (process_onSphere hN β g hg x hx)
  have ht := GlobalSDE.process_timeCut (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x T
  filter_upwards [hp,ht] with q hq htq
  intro hqt
  change ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set (VectorBrownian.Space N))).indicator
    (fun p => process β g hg x p.1 p.2)) q =
      (stateClass β g hg x T : Lp (State N) 2
        (nonnegativeLebesgueMeasure.prod (VectorBrownian.law N))) q at htq
  rw [← htq,indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ
    (univ : Set (VectorBrownian.Space N)) from ⟨hqt,mem_univ _⟩)]
  exact hq q.1

private theorem sphere_cutoff_bound {z : State N} (hz : OnSphere z) :
    ‖z‖≤cutoffRadius N := by
  have hsq := (onSphere_iff_norm_sq z).mp hz
  nlinarith [norm_nonneg z,(cutoffRadius N).coe_nonneg,cutoffRadius_contains_sphere N]

theorem cutoffDrift_sub_bound_onSphere (β : ℝ) (g c : State N → State N)
    (δ : ℝ) (hcb : ∀ z,OnSphere z → ‖drift β c z-drift β g z‖≤δ)
    (i : Fin N) (z : State N) (hz : OnSphere z) :
    ‖cutoffDrift β c (cutoffRadius N) (cutoffRadius_pos N) i z-
      cutoffDrift β g (cutoffRadius N) (cutoffRadius_pos N) i z‖≤δ := by
  rw [cutoffDrift_eq β c _ (cutoffRadius_pos N) z (sphere_cutoff_bound hz),
    cutoffDrift_eq β g _ (cutoffRadius_pos N) z (sphere_cutoff_bound hz),← PiLp.sub_apply]
  exact (PiLp.norm_apply_le _ i).trans (hcb z hz)

theorem stateClass_drift_bound (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) : ∃ K : ℝ≥0,
    ∀ (c : State N → State N) (hc : ContDiff ℝ 1 c) (δ : ℝ) (hδ : 0≤δ)
      (hcb : ∀ z,OnSphere z → ‖drift β c z-drift β g z‖≤δ)
      (x : State N) (hx : OnSphere x),
      ‖stateClass β c hc x T-stateClass β g hg x T‖≤(K : ℝ)*δ := by
  obtain ⟨K,hK⟩ := sourceClass_drift_bound_on_class
    (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec T
  refine ⟨K,fun c hc δ hδ hcb x hx => ?_⟩
  apply hK (cutoffDrift_lipschitz β c hc (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (initialClass x T) δ hδ
  intro i
  filter_upwards [stateClass_onSphere hN β c hc x hx T] with q hq
  intro hqt
  exact cutoffDrift_sub_bound_onSphere β g c δ hcb i _ (hq hqt)

theorem stateClass_tendsto_of_drift (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (c : ℕ → State N → State N)
    (hc : ∀ k,ContDiff ℝ 1 (c k)) (δ : ℕ → ℝ) (hδ : ∀ k,0≤δ k)
    (hcb : ∀ k z,OnSphere z → ‖drift β (c k) z-drift β g z‖≤δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    Tendsto (fun k => stateClass β (c k) (hc k) x T) atTop
      (𝓝 (stateClass β g hg x T)) := by
  obtain ⟨K,hK⟩ := stateClass_drift_bound hN β g hg T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _)
    (fun k => hK (c k) (hc k) (δ k) (hδ k) (hcb k) x hx)
  simpa only [mul_zero] using hlim.const_mul (K : ℝ)

def driftClass (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (T : ℝ≥0) (i : Fin N) :=
  predictableCoefficient
    ((cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec i)
    (stateClass β g hg x T) T

def noiseClass (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (T : ℝ≥0) (i j : Fin N) :=
  predictableCoefficient
    ((CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec i j)
    (stateClass β g hg x T) T

/-- Actual terminal L² representative assembled from the true full-filtration
drift and Itô integrals. -/
def terminalValue (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (T t : ℝ≥0) : Lp (State N) 2 (VectorBrownian.law N) :=
  terminalClass (NullAugmentation.driver (VectorBrownian.driver N)) x
    (driftClass β g hg x T) (noiseClass β g hg x T) T t

theorem terminalValue_ae (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (T t : ℝ≥0) (ht : t≤T) :
    (terminalValue β g hg x T t : VectorBrownian.Space N → State N) =ᵐ[VectorBrownian.law N]
      process β g hg x t := by
  have h := nonlinear_terminalClass_ae (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    x T t (stateClass β g hg x T)
  have he := GlobalSDE.process_eq_horizon (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x T
  exact h.trans (he.mono (fun _ h => (h t ht).symm))

theorem driftClass_tendsto_of_drift (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (c : ℕ → State N → State N)
    (hc : ∀ k,ContDiff ℝ 1 (c k)) (δ : ℕ → ℝ) (hδ : ∀ k,0≤δ k)
    (hcb : ∀ k z,OnSphere z → ‖drift β (c k) z-drift β g z‖≤δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (i : Fin N) :
    Tendsto (fun k => driftClass β (c k) (hc k) x T i) atTop
      (𝓝 (driftClass β g hg x T i)) := by
  let Kb := (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose
  let hb := (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
  have hstate := tendsto_iff_norm_sub_tendsto_zero.mp
    (stateClass_tendsto_of_drift hN β g hg c hc δ hδ hcb hlim x hx T)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _)
    (g := fun k => δ k*(initialScale (P := VectorBrownian.law N) T : ℝ)+
      (Kb : ℝ)*‖stateClass β (c k) (hc k) x T-stateClass β g hg x T‖)
  · intro k
    let U := stateClass β (c k) (hc k) x T
    let V := stateClass β g hg x T
    let hd := (cutoffDrift_lipschitz β (c k) (hc k) (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    have hdif : ‖predictableCoefficient (hd i) U T-predictableCoefficient (hb i) U T‖≤
        δ k*(initialScale (P := VectorBrownian.law N) T : ℝ) := by
      apply coefficient_sub_norm_bound_on_class (hb i) (hd i) U T (δ k) (hδ k)
      filter_upwards [stateClass_onSphere hN β (c k) (hc k) x hx T] with q hq
      intro hqt
      exact cutoffDrift_sub_bound_onSphere β g (c k) (δ k) (hcb k) i _ (hq hqt)
    exact (norm_sub_le_norm_sub_add_norm_sub _ (predictableCoefficient (hb i) U T) _).trans
      (add_le_add hdif (norm_predictableCoefficient_sub_le (hb i) U V T))
  · simpa only [zero_mul,mul_zero,add_zero] using
      (hlim.mul_const (initialScale (P := VectorBrownian.law N) T : ℝ)).add
        (hstate.const_mul (Kb : ℝ))

theorem noiseClass_tendsto_of_drift (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (c : ℕ → State N → State N)
    (hc : ∀ k,ContDiff ℝ 1 (c k)) (δ : ℕ → ℝ) (hδ : ∀ k,0≤δ k)
    (hcb : ∀ k z,OnSphere z → ‖drift β (c k) z-drift β g z‖≤δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (i j : Fin N) :
    Tendsto (fun k => noiseClass β (c k) (hc k) x T i j) atTop
      (𝓝 (noiseClass β g hg x T i j)) := by
  let hs := (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec i j
  have hL : LipschitzWith
      (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose
      (fun U : PredictableStateL2 N
        (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))
        (VectorBrownian.law N) => predictableCoefficient hs U T) :=
    LipschitzWith.of_dist_le_mul (fun U V => by
      simpa only [dist_eq_norm] using norm_predictableCoefficient_sub_le hs U V T)
  exact hL.continuous.tendsto _ |>.comp
    (stateClass_tendsto_of_drift hN β g hg c hc δ hδ hcb hlim x hx T)

/-- The literal Brownian terminal states converge in L² under uniform
sphere drift convergence. Stationarity is not used in this theorem. -/
theorem terminalValue_tendsto_of_drift (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (c : ℕ → State N → State N)
    (hc : ∀ k,ContDiff ℝ 1 (c k)) (δ : ℕ → ℝ) (hδ : ∀ k,0≤δ k)
    (hcb : ∀ k z,OnSphere z → ‖drift β (c k) z-drift β g z‖≤δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : State N) (hx : OnSphere x) (T t : ℝ≥0) :
    Tendsto (fun k => terminalValue β (c k) (hc k) x T t) atTop
      (𝓝 (terminalValue β g hg x T t)) := by
  unfold terminalValue terminalClass
  apply Tendsto.add tendsto_const_nhds
  apply tendsto_finset_sum
  intro i _
  apply (stateTerminalInclusion i).continuous.tendsto _ |>.comp
  apply Tendsto.add
  · exact (driftTerminalOperator T t).continuous.tendsto _ |>.comp
      (driftClass_tendsto_of_drift hN β g hg c hc δ hδ hcb hlim x hx T i)
  · apply tendsto_finset_sum
    intro j _
    exact (itoTerminalOperator (NullAugmentation.driver (VectorBrownian.driver N)) j t).continuous.tendsto _ |>.comp
      (noiseClass_tendsto_of_drift hN β g hg c hc δ hδ hcb hlim x hx T i j)

/-- Convergence of literal transition expectations for every bounded
continuous observable, under the actual common Brownian law. -/
theorem expectation_tendsto_of_drift (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (c : ℕ → State N → State N)
    (hc : ∀ k,ContDiff ℝ 1 (c k)) (δ : ℕ → ℝ) (hδ : ∀ k,0≤δ k)
    (hcb : ∀ k z,OnSphere z → ‖drift β (c k) z-drift β g z‖≤δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : State N) (hx : OnSphere x) (t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ z,‖f z‖≤C) :
    Tendsto (fun k => ∫ ω,f (process β (c k) (hc k) x t ω) ∂VectorBrownian.law N)
      atTop (𝓝 (∫ ω,f (process β g hg x t ω) ∂VectorBrownian.law N)) := by
  have ht := (ActualSphereFeller.observable_continuous f hf C hC).tendsto _ |>.comp
    (terminalValue_tendsto_of_drift hN β g hg c hc δ hδ hcb hlim x hx t t)
  have he (a : State N → State N) (ha : ContDiff ℝ 1 a) :
      GaussianObservableDerivative.observable f (terminalValue β a ha x t t)=
        ∫ ω,f (process β a ha x t ω) ∂VectorBrownian.law N :=
    integral_congr_ae ((terminalValue_ae β a ha x t t le_rfl).mono (fun _ h => congrArg f h))
  simpa only [Function.comp_def,he] using ht

end SlowEquilibration.SphericalC1Dynamics
