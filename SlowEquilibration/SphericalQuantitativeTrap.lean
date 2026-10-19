-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalStationaryTrap

/-!
# Quantitative deterministic trapping in the physical diffusion

This module assembles conclusions (iv) and (v) of the memory proof from its
literal deterministic energy, alignment and cap inputs. It does not assert
the stochastic pressure estimates needed to produce those inputs. The
source choices of time, radius, tolerance and constants are explicit.
-/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalQuantitativeTrap

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalPhysicalSpectral
open SphericalForm SphericalBarycenter SphericalLaplaceIdentification SphericalStationaryTrap
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal Topology InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

def memoryTime (γ : ℝ) (N : ℕ) : ℝ≥0 := ⟨Real.exp (γ * N), (Real.exp_pos _).le⟩
def startingErrorConstant (CE q₁ : ℝ) : ℝ := 32 * CE / q₁ ^ 2
def capErrorConstant (s₀ : ℝ) : ℝ := 1 + 2 / s₀

lemma capMassSup_le (π : Measure (Vector N)) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ v ∂π, OnSphere v) {s C : ℝ}
    (hcap : ∀ v, OnSphere v → π.real (cap v s) ≤ C) : capMassSup π s ≤ C := by
  obtain ⟨v, hv⟩ := hπ.exists
  apply csSup_le
  · exact ⟨π.real (cap v s), v, hv, rfl⟩
  · rintro r ⟨w, hw, rfl⟩
    exact hcap w hw

/-- Exact finite-dimensional form of `eq:mem-X`, `eq:mem-tv` and the first
entropy inequality of the memory proof. The source energy exponent is
4γ, so γ=c_E/4 is encoded without a further asymptotic premise. -/
theorem quantitative_trap (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (G : Set (Vector N)) (hG : MeasurableSet G)
    {γ a c₀ θ CE q₁ s₀ : ℝ} (hγ : 0 < γ) (hCE : 0 ≤ CE)
    (hq : 0 < q₁) (hs : 0 < s₀) (hsq : s₀ ≤ q₁ / 2)
    (hθa : θ ≤ a) (hθc : θ ≤ c₀)
    (hEnergy : vectorDirichletEnergy β (potential μ J) B ≤ CE * Real.exp (-4 * γ * N))
    (hBad : (mixtureGibbsLaw μ β J).real Gᶜ ≤ Real.exp (-a * N))
    (hCap : ∀ v, OnSphere v → (mixtureGibbsLaw μ β J).real (cap v s₀) ≤
      (2 / s₀) * Real.exp (-c₀ * N))
    (hB : ∀ y, OnSphere y → ‖B y‖ ≤ 1)
    (hA : ∀ y ∈ G, OnSphere y → 3 * q₁ / 4 ≤ inner ℝ (spin y) (B y)) :
    ∃ X : Set (Vector N), MeasurableSet X ∧ X ⊆ {x | OnSphere x} ∧
      (mixtureGibbsLaw μ β J).real Xᶜ ≤ Real.exp (-a * N) +
        startingErrorConstant CE q₁ * Real.exp (-2 * γ * N) ∧
      ∀ x ∈ X, ∀ t ≤ memoryTime γ N,
        1 - Real.exp (-γ * N) - capErrorConstant s₀ * Real.exp (-θ * N) ≤
          totalVariation (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) ∧
        ENNReal.ofReal ((1 - Real.exp (-γ * N)) * (θ * N - Real.log (capErrorConstant s₀)) - Real.log 2) ≤
          InformationTheory.klDiv (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) := by
  have hN1 : 1 ≤ N := by omega
  let _ := mixtureGibbsLaw_probability hN1 μ β J
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hρ : 0 < q₁ / 4 := by positivity
  have hη : 0 < Real.exp (-γ * N) := Real.exp_pos _
  have hη1 : Real.exp (-γ * N) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  let Y := SphericalStationaryTrap.goodStartingSet μ J β (memoryTime γ N) B (q₁ / 4) (Real.exp (-γ * N))
  have hYm : MeasurableSet Y :=
    SphericalStationaryTrap.goodStartingSet_measurable μ J β _ hBs.continuous.measurable _ _
  have hY : (mixtureGibbsLaw μ β J).real Yᶜ ≤
      startingErrorConstant CE q₁ * Real.exp (-2 * γ * N) := by
    have hbase := SphericalStationaryTrap.goodStartingSet_compl_mass_le hN1 μ J β
      (memoryTime γ N) hBs.continuous.measurable hρ hη
      (smooth_vector_stationary_displacement_integrable hN1 μ J β B hBs _)
      (smooth_vector_stationary_displacement_energy_le hN μ J β B hBs _)
    apply hbase.trans
    change 2 * Real.exp (γ * N) * vectorDirichletEnergy β (potential μ J) B /
      ((q₁ / 4) ^ 2 * Real.exp (-γ * N)) ≤ _
    calc
      _ ≤ 2 * Real.exp (γ * N) * (CE * Real.exp (-4 * γ * N)) /
          ((q₁ / 4) ^ 2 * Real.exp (-γ * N)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hEnergy (by positivity)
      _ = startingErrorConstant CE q₁ * Real.exp (-2 * γ * N) := by
        have he : Real.exp (γ * N) * Real.exp (-4 * γ * N) /
            Real.exp (-γ * N) = Real.exp (-2 * γ * N) := by
          rw [← Real.exp_add, ← Real.exp_sub]
          congr 1
          ring
        calc
          _ = (32 * CE / q₁ ^ 2) * (Real.exp (γ * N) * Real.exp (-4 * γ * N) /
              Real.exp (-γ * N)) := by field_simp; ring
          _ = _ := by rw [he]; rfl
  have hCM : 0 < capErrorConstant s₀ := by dsimp [capErrorConstant]; positivity
  have hcapSup : capMassSup (mixtureGibbsLaw μ β J) (q₁ / 2) ≤
      (2 / s₀) * Real.exp (-c₀ * N) := by
    apply capMassSup_le _ (mixtureGibbsLaw_onSphere hN1 μ J β)
    intro v hv
    exact (measureReal_mono (show cap v (q₁ / 2) ⊆ cap v s₀ from
      fun y hy => hsq.trans hy)).trans (hCap v hv)
  have hw : (mixtureGibbsLaw μ β J).real Gᶜ + capMassSup (mixtureGibbsLaw μ β J) (q₁ / 2) ≤
      capErrorConstant s₀ * Real.exp (-θ * N) := by
    have hae : Real.exp (-a * N) ≤ Real.exp (-θ * N) :=
      Real.exp_le_exp.mpr (by nlinarith [hθa])
    have hce : Real.exp (-c₀ * N) ≤ Real.exp (-θ * N) :=
      Real.exp_le_exp.mpr (by nlinarith [hθc])
    calc
      _ ≤ Real.exp (-a * N) + (2 / s₀) * Real.exp (-c₀ * N) := add_le_add hBad hcapSup
      _ ≤ Real.exp (-θ * N) + (2 / s₀) * Real.exp (-θ * N) :=
        add_le_add hae (mul_le_mul_of_nonneg_left hce (by positivity))
      _ = _ := by dsimp [capErrorConstant]; ring
  refine ⟨G ∩ Y, hG.inter hYm, fun x hx => hx.2.1, ?_, ?_⟩
  · rw [compl_inter]
    exact (measureReal_union_le _ _).trans (add_le_add hBad hY)
  · intro x hx t ht
    have hMass := imageBall_gibbs_mass_le hN1 μ J β B G (3 * q₁ / 4) (q₁ / 4)
      hρ.le (by linarith) hB hA x hx.2.1 hx.1
    have hthreshold : 3 * q₁ / 4 - q₁ / 4 = q₁ / 2 := by ring
    rw [hthreshold] at hMass
    have htest := StationaryTrap.endpoint_separation_all_times
      (mixedTransitionKernel μ J β) (mixtureGibbsLaw μ β J) (physical_semigroup μ J β)
      (mixedTransitionKernel_gibbs_invariant hN1 μ J β) (memoryTime γ N) x
      (StationaryTrap.imageBall_measurable hBs.continuous.measurable (q₁ / 4) x)
      hη1.le (mul_pos hCM (Real.exp_pos _))
      (StationaryTrap.imageBall_transition_mass _ hBs.continuous.measurable _ _ hx.2.2)
      (hMass.trans hw) t ht
    have hlog : Real.log (1 / (capErrorConstant s₀ * Real.exp (-θ * N))) =
        θ * N - Real.log (capErrorConstant s₀) := by
      rw [one_div, Real.log_inv, Real.log_mul hCM.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    simpa only [hlog] using htest

private lemma exp_decay (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun N : ℕ => Real.exp (-γ * N)) atTop (𝓝 (0 : ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hγ) using 1
  ext N
  simp only [Function.comp_apply, neg_mul]

/-- The actual scalar entropy threshold in conclusion (v), with every
constant fixed before the dimension tends to infinity. -/
theorem entropy_trial_eventually_linear {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      θ * N / 2 ≤ (1 - Real.exp (-γ * N)) * (θ * N - Real.log C) - Real.log 2 := by
  have hsize : Tendsto (fun N : ℕ => θ * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hθ
  filter_upwards [(exp_decay γ hγ).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
    hsize.eventually_ge_atTop (4 * (|Real.log C| + Real.log 2))] with N hsmall hlarge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have habs := le_abs_self (Real.log C)
  have hpos : 0 ≤ θ * (N : ℝ) - Real.log C := by linarith [abs_nonneg (Real.log C)]
  have hmul := mul_le_mul_of_nonneg_right (show (3 / 4 : ℝ) ≤ 1 - Real.exp (-γ * N) by linarith)
    hpos
  nlinarith [abs_nonneg (Real.log C)]

/-- Integrating actual pointwise kernel entropy over a Gibbs set of mass
at least one half gives the source information bound. -/
theorem stationary_information_lower (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0)
    {X : Set (Vector N)} (hX : MeasurableSet X) {L : ℝ} (hL : 0 ≤ L)
    (hMass : 1 / 2 ≤ (mixtureGibbsLaw μ β J).real X)
    (hKL : ∀ x ∈ X, ENNReal.ofReal L ≤
      InformationTheory.klDiv (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J)) :
    ENNReal.ofReal (L / 2) ≤
      endpointMutualInformation (mixtureGibbsLaw μ β J) (mixedTransitionKernel μ J β t) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  rw [stationary_endpoint_mutualInformation _ _ (mixedTransitionKernel_gibbs_invariant hN μ J β t)]
  calc
    ENNReal.ofReal (L / 2) ≤ ENNReal.ofReal L * (mixtureGibbsLaw μ β J) X := by
      have hreal : ENNReal.ofReal ((mixtureGibbsLaw μ β J).real X) = (mixtureGibbsLaw μ β J) X :=
        ENNReal.ofReal_toReal (measure_ne_top _ _)
      rw [← hreal, ← ENNReal.ofReal_mul hL]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    _ = ∫⁻ x, X.indicator (fun _ => ENNReal.ofReal L) x ∂mixtureGibbsLaw μ β J :=
      (lintegral_indicator_const hX _).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ X
      · simpa only [indicator_of_mem hx] using hKL x hx
      · simp [hx]

/-- The dimension threshold is uniform in the field and the observable.
Under the source deterministic inputs, actual pointwise entropy is at
least θN/2 and actual stationary endpoint information at least θN/4. -/
theorem quantitative_trap_eventually (μ : FiniteMixture) (β : ℝ)
    {γ a c₀ θ CE q₁ s₀ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) (hCE : 0 ≤ CE)
    (hq : 0 < q₁) (hs : 0 < s₀) (hsq : s₀ ≤ q₁ / 2)
    (hθa : θ ≤ a) (hθc : θ ≤ c₀) :
    ∀ᶠ N : ℕ in atTop, ∀ (J : Disorder N μ.maxDegree)
      (B : Vector N → Vector N) (_ : ContDiff ℝ 1 B)
      (G : Set (Vector N)) (_ : MeasurableSet G),
      vectorDirichletEnergy β (potential μ J) B ≤ CE * Real.exp (-4 * γ * N) →
      (mixtureGibbsLaw μ β J).real Gᶜ ≤ Real.exp (-a * N) →
      (∀ v, OnSphere v → (mixtureGibbsLaw μ β J).real (cap v s₀) ≤ (2 / s₀) * Real.exp (-c₀ * N)) →
      (∀ y, OnSphere y → ‖B y‖ ≤ 1) →
      (∀ y ∈ G, OnSphere y → 3 * q₁ / 4 ≤ inner ℝ (spin y) (B y)) →
      ∃ X : Set (Vector N), MeasurableSet X ∧ X ⊆ {x | OnSphere x} ∧
        (mixtureGibbsLaw μ β J).real Xᶜ ≤ Real.exp (-a * N) +
          startingErrorConstant CE q₁ * Real.exp (-2 * γ * N) ∧
        (∀ x ∈ X, ∀ t ≤ memoryTime γ N,
          1 - Real.exp (-γ * N) - capErrorConstant s₀ * Real.exp (-θ * N) ≤
            totalVariation (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) ∧
          ENNReal.ofReal (θ * N / 2) ≤
            InformationTheory.klDiv (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J)) ∧
        ∀ t ≤ memoryTime γ N,
          ENNReal.ofReal (θ * N / 4) ≤
            endpointMutualInformation (mixtureGibbsLaw μ β J) (mixedTransitionKernel μ J β t) := by
  have ha : 0 < a := hθ.trans_le hθa
  have hdecay : Tendsto (fun N : ℕ => Real.exp (-a * N) +
      startingErrorConstant CE q₁ * Real.exp (-2 * γ * N)) atTop (𝓝 (0 : ℝ)) := by
    convert (exp_decay a ha).add ((exp_decay (2 * γ) (by positivity)).const_mul
      (startingErrorConstant CE q₁)) using 1 <;> simp only [mul_zero, add_zero, neg_mul, mul_assoc]
  filter_upwards [eventually_ge_atTop 2,
    entropy_trial_eventually_linear hγ hθ (capErrorConstant s₀),
    hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with N hN hEntropy hsmall
  intro J B hBs G hG hEnergy hBad hCap hB hA
  let _ := mixtureGibbsLaw_probability (show 1 ≤ N by omega) μ β J
  obtain ⟨X, hXm, hXs, hXbad, hsep⟩ := quantitative_trap hN μ J β B hBs G hG
    hγ hCE hq hs hsq hθa hθc hEnergy hBad hCap hB hA
  have hLinear : ∀ x ∈ X, ∀ t ≤ memoryTime γ N,
      1 - Real.exp (-γ * N) - capErrorConstant s₀ * Real.exp (-θ * N) ≤
        totalVariation (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) ∧
      ENNReal.ofReal (θ * N / 2) ≤
        InformationTheory.klDiv (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) := by
    intro x hx t ht
    exact ⟨(hsep x hx t ht).1, (ENNReal.ofReal_le_ofReal hEntropy).trans (hsep x hx t ht).2⟩
  refine ⟨X, hXm, hXs, hXbad, hLinear, ?_⟩
  intro t ht
  have hcomp := probReal_add_probReal_compl (μ := mixtureGibbsLaw μ β J) hXm
  have hMass : 1 / 2 ≤ (mixtureGibbsLaw μ β J).real X := by linarith
  have hinfo := stationary_information_lower (show 1 ≤ N by omega) μ J β t hXm
    (show 0 ≤ θ * (N : ℝ) / 2 by positivity) hMass (fun x hx => (hLinear x hx t ht).2)
  convert hinfo using 1
  congr 1
  ring

end SlowEquilibration.SphericalQuantitativeTrap
