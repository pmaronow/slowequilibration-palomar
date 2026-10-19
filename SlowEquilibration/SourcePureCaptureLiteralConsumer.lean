-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureWindowTransport
public import SlowEquilibration.SourcePureCaptureFromPhysicalInputs

/-! The pure capture theorem in the literal consumer notation C_{N,M},
including the radial-U window, the center-field energy normalization,
and both the fixed-width and microscopic source quantifiers. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureCaptureLiteralConsumer
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalTAPCertificate PureStationarity SphericalPureCapSourceScalars TwoAtomStationarity
open SourcePureCaptureFixedCapEstimates SourcePureCaptureFromCoarseCover
open SourcePureCaptureWindowTransport SourcePureCaptureFromPhysicalInputs
open PureCapturePhysicalCoarseDiniAssembly
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The scale in the literal consumer expectation is exactly the printed
source center `N E₀ - log N / (2 c₀)`, with c₀=βx. -/
theorem pure_source_consumer_center_eq
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (d : ℕ) :
    (Real.sqrt Q)^p*pureSourceCenter p hp d =
      (d+2:ℕ)*markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q-
        Real.log (d+2:ℕ)/(2*(β*x)) := by
  obtain ⟨hE,hc⟩ := sourcePure_certificate_scalar_coordinates p hp h
  rw [hE]
  dsimp only [pureSourceCenter]
  rw [← hc]
  field_simp [h.beta_pos.ne',h.weight_range.1.ne',
    (pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p).ne']

/-- Any prescribed source radial window with the contact in its interior
accepts the transport. Closedness or an exterior lower edge can be imposed
by the consumer independently of this deterministic identity. -/
theorem pure_source_contact_interior
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {U : Set ℝ}
    (hU : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U) :
    (p:ℝ)*(Real.sqrt Q)^p*pureEnergyConstant p (by omega) ∈ interior U := by
  have hK := PairConditionalDeterminantMoments.source_pure_markK_eq_degree_mul_markE
    p (by omega) 1 (by positivity) h
  obtain ⟨hE,_⟩ := sourcePure_certificate_scalar_coordinates p hp h
  rw [hK,hE] at hU
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hU

/-- Exact source microscopic quantifiers for the center-field critical
set C_{N,M}, after the original-energy capture statement has been proved. -/
theorem pure_consumer_microscopic_capture_of_original
    (p : ℕ) (hp : 4 ≤ p) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (U : Set ℝ)
    (hU : (p:ℝ)*(Real.sqrt Q)^p*pureEnergyConstant p (by omega) ∈ interior U)
    (hCapture : ∀ ε : ℝ, 0 < ε → ∃ L w : ℝ, 0 < L ∧ 0 < w ∧
      ∀ L' w' : ℝ, L ≤ L' → w ≤ w' →
        Filter.limsup (pureMicroscopicUncovered p hp β Q L' w') atTop ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ w₀ : ℝ, 0 < M₀ ∧ 0 < w₀ ∧
      ∀ M w : ℝ, M₀ ≤ M → w₀ ≤ w →
        Filter.limsup (fun d => pureConsumerUncovered p hp β Q M
          (w/Real.sqrt (d+2:ℕ)) U d) atTop ≤ ε := by
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr hQ) p
  intro ε hε
  obtain ⟨L,w₀,hL,hw₀,hcap⟩ := hCapture ε hε
  refine ⟨s*L,w₀,mul_pos hs hL,hw₀,?_⟩
  intro M w hM hw
  have hLM : L ≤ M/s := (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hM)
  have heq := pureConsumerUncovered_eventually_eq_original p hp β hQ (M/s)
    (fun d => w/Real.sqrt (d+2:ℕ)) U hU
  have hscale : (Real.sqrt Q)^p*(M/s)=M := by
    change s*(M/s)=M
    field_simp [hs.ne']
  simp only [hscale] at heq
  rw [Filter.limsup_congr heq]
  exact hcap (M/s) w hLM hw

/-- Fixed-width capture in the literal C_{N,M} notation; b and U are
fixed before M and the dimension. -/
theorem pure_consumer_fixed_capture_of_original
    (p : ℕ) (hp : 4 ≤ p) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (U : Set ℝ)
    (hU : (p:ℝ)*(Real.sqrt Q)^p*pureEnergyConstant p (by omega) ∈ interior U)
    (b : ℝ)
    (hCapture : Tendsto (fun L : ℝ => Filter.limsup
      (pureFixedBandUncovered p hp β Q L b) atTop) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun M : ℝ => Filter.limsup
      (pureConsumerUncovered p hp β Q M b U) atTop) atTop (𝓝 (0:ℝ)) := by
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr hQ) p
  have hh := hCapture.comp (tendsto_id.atTop_div_const hs)
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro M
  have heq := pureConsumerUncovered_eventually_eq_original p hp β hQ
    (M/s) (fun _ => b) U hU
  have hscale : (Real.sqrt Q)^p*(M/s)=M := by
    change s*(M/s)=M
    field_simp [hs.ne']
  simp only [hscale] at heq
  exact (Filter.limsup_congr heq).symm

/-- Both conclusions of source `thm:pc-capture` for any prescribed radial
window U containing K₀ in its interior, from exactly the three remaining
physical inputs to the coarse cover. The small width bound is chosen before
both the energy window and the dimension. -/
theorem pure_consumer_capture_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (U : Set ℝ)
    (hU : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    (∃ b₀ : ℝ, b₀ ∈ Ioo (0:ℝ) (Real.sqrt Q) ∧
      ∀ b : ℝ, b ∈ Ioc (0:ℝ) b₀ → Tendsto
        (fun M : ℝ => Filter.limsup (pureConsumerUncovered p hp β Q M b U) atTop)
        atTop (𝓝 (0:ℝ))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M₀ w₀ : ℝ, 0 < M₀ ∧ 0 < w₀ ∧
      ∀ M w : ℝ, M₀ ≤ M → w₀ ≤ w →
        Filter.limsup (fun d => pureConsumerUncovered p hp β Q M
          (w/Real.sqrt (d+2:ℕ)) U d) atTop ≤ ε) := by
  have hcontact := pure_source_contact_interior p hp h hU
  obtain ⟨hmicro,hfixed⟩ :=
    pure_original_capture_of_three_physical_inputs p hp h hNorm hMean hRelocate
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr h.overlap_range.1
  constructor
  · refine ⟨Real.sqrt Q/2,⟨half_pos hroot,by linarith⟩,?_⟩
    intro b hb
    exact pure_consumer_fixed_capture_of_original p hp β h.overlap_range.1 U hcontact
      b (hfixed b hb.1)
  · exact pure_consumer_microscopic_capture_of_original p hp β h.overlap_range.1 U
      hcontact hmicro

end SlowEquilibration.SourcePureCaptureLiteralConsumer
