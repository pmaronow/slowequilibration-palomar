-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceInitialBandFieldAdapter
public import SlowEquilibration.SourceConditionedCPTransferUnconditional

/-! The quantitative uniform-start input for manuscript `thm:main-initial`
(ii)/(iii) and `cor:cp-information`. The source CP transfer supplies one
exponential horizon for every fixed critical-center window and Holder
order. We retain its polynomial entry rates, transport Gibbs capture to
actual fields, and remove the source dimension shift, while preserving
the uniform-start separation conclusion at the same horizon. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceInitialQuantitativeInput

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalOverlapExponential
open SourceInitialBandFieldAdapter SourceReductionConsumerBandBound
open SourceReductionConsumerAsymptotic SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptoticTimeSup SourceReductionPathMarginal
open SphericalRealTimePathKernel SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal

set_option autoImplicit false

/-- The source CP exponent before the loss from the Holder order. -/
def alpha (μ : FiniteMixture) : ℝ :=
  ((μ.minDegree : ℝ) - 2) / 2

/-- The common band family, capture and polynomial entry rates consumed
by the menu, conditional entropy and mutual-information reductions. -/
structure QuantitativeUniformStart
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (B : ∀ N, ℝ → Set (SphericalFieldKernels.Field N μ × Vector N)) :
    Prop where
  degree : 4 ≤ μ.minDegree
  measurable : ∀ N M, MeasurableSet (B N M)
  rotation : ∀ M : ℝ, 0 < M → ∀ N, 2 ≤ N →
    ∀ (V : Vector N ≃ₗᵢ[ℝ] Vector N)
      (H : SphericalFieldKernels.Field N μ),
      Prod.mk (SphericalFullFieldPathKernel.fieldRotation μ V H) ⁻¹'
        B N M =
      V '' (Prod.mk H ⁻¹' B N M)
  capture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ N in atTop,
      (∫ H,
        (SphericalFieldKernels.gibbsKernel μ β H).real
          (Prod.mk H ⁻¹' B N M)ᶜ
        ∂SphericalFieldKernels.fieldLaw N μ) < η
  rate : ∀ M r : ℝ, 0 < M → 1 < r →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop,
      SphericalFieldKernels.uniformEntryMass μ β (T N) (B N M) ≤
        C * (N : ℝ) ^ (-alpha μ * (1 - 1/r))

/-- The literal source bands in ordinary dimensions; at dimension
`n + 2` their energy center is exactly the source center `m n`. -/
def sourceBands (μ : FiniteMixture) (Q : ℝ)
    (m : ℕ → ℝ) (b : ℝ) (U : Set ℝ) :
    ∀ N, ℝ → Set (SphericalFieldKernels.Field N μ × Vector N) :=
  fun N M => sourceBand μ Q (m (N-2)) M b U

private theorem eventually_of_add_two {P : ℕ → Prop}
    (h : ∀ᶠ n : ℕ in atTop, P (n+2)) : ∀ᶠ N : ℕ in atTop, P N := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨n₀+2, fun N hN => ?_⟩
  have h := hn₀ (N-2) (by omega)
  simpa only [Nat.sub_add_cancel (show 2 ≤ N by omega)] using h

private theorem endpoint_mean_le_timeSup {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q m M b β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) :
    (∫ J, (mixedTransitionKernel μ J β T ∘ₘ sphereLaw N).real
      (ambientWindowBandUnion μ Q m M b U J) ∂disorderLaw N μ.maxDegree) ≤
    ∫ J, originalBandTimeSup μ Q m M b β U T J
      ∂disorderLaw N μ.maxDegree := by
  let _ := sphereLaw_probability N
  apply integral_mono_of_nonneg (.of_forall fun _ => measureReal_nonneg)
    (originalBandTimeSup_integrable hN μ Q m M b β hU T)
  apply Eventually.of_forall
  intro J
  let t : RealPathTime T := ⟨T, ⟨T.coe_nonneg, le_rfl⟩⟩
  have ht : nnrealTime t = T := Subtype.ext rfl
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact measureReal_le_one
  · exact ⟨t, by rw [ht]⟩

/-- Source `prop:cp-transfer` at one common horizon, retaining the
quantitative input for `thm:main-initial` (ii)/(iii) and the information
corollary, together with its original uniform-start consequence. -/
theorem quantitative_uniformStart_of_source_inputs
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hβ : 0 ≤ β)
    (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2 * Real.sqrt (Q^2 * μ.xi2 Q) < k)
    (m : ℕ → ℝ)
    (hm : Tendsto
      (fun n : ℕ => m n / ((n+2 : ℕ) : ℝ)) atTop (𝓝 E))
    (hcount : ∀ M : ℝ, 0 < M →
      limsup
        (SourceReductionConsumerAsymptoticCounts.originalWindowExpectedCount
          μ Q m M U) atTop < ⊤)
    (hcapture : Tendsto
      (fun M : ℝ => limsup
        (fun n : ℕ =>
          ∫ J,
            SourceReductionConsumerAsymptotic.originalBandComplementMass
              μ Q (m n) M b β U J
            ∂disorderLaw (n+2) μ.maxDegree)
        atTop)
      atTop (𝓝 0)) :
    ∃ γ : ℝ, 0 < γ ∧
      QuantitativeUniformStart μ β
        (fun N => exponentialGridHorizon γ N)
        (sourceBands μ Q m b U) ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n =>
          SourceReductionConsumerAsymptotic.originalUniformIntervalDistance
            μ β (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) := by
  obtain ⟨a, γ, _ha, _hag, hγ, htransfer⟩ :=
    SourceConditionedCPTransferUnconditional.source_cp_transfer
      μ hd hQ hQ1 hβ hb U hU hgap
  obtain ⟨hrate, hseparation⟩ := htransfer m hm hcount
  refine ⟨γ, hγ, ?_, hseparation hcapture⟩
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · intro N M
    exact (sourceBand_isClosed μ Q (m (N-2)) M b hU.isClosed).measurableSet
  · intro M _hM N _hN V H
    exact sourceBand_rotation μ hQ.le (m (N-2)) M b U V H
  · intro η hη
    obtain ⟨M, hM, hcaptureM⟩ := fixed_window_of_iterated_limsup
      (fun n M => ∫ J, originalBandComplementMass μ Q (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) (by
          intro M _hM n
          have hi := integral_mono
            (originalBandComplementMass_integrable (N := n+2)
              (by omega) μ Q (m n) M b β hU.isClosed)
            (integrable_const (1 : ℝ))
            (fun J => (originalBandComplementMass_mem_unit
              (by omega) μ Q (m n) M b β U J).2)
          simpa using hi) hcapture η hη
    refine ⟨M, hM, eventually_of_add_two ?_⟩
    filter_upwards [hcaptureM] with n hn
    simpa only [sourceBands, Nat.add_sub_cancel,
      sourceBand_capture_integral_eq (N := n+2)
        (by omega) μ hQ.le (m n) M b β hU.isClosed] using hn
  · intro M r hM hr
    obtain ⟨C, hC, hrateM⟩ := hrate M r hM hr
    refine ⟨C, hC, eventually_of_add_two ?_⟩
    filter_upwards [hrateM] with n hn
    simp only [sourceBands, Nat.add_sub_cancel]
    rw [sourceBand_uniformEntryMass_eq (by omega) μ hQ.le (m n) M b β hU.isClosed]
    exact (endpoint_mean_le_timeSup (by omega) μ Q (m n) M b β hU.isClosed
      (exponentialGridHorizon γ (n+2))).trans (hn.1.trans hn.2)

end SlowEquilibration.SourceInitialQuantitativeInput
