-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureDenominatorFixedCapTransfer

/-! The right-hand `η↓0` formulation of the generic pure denominator
transfer for any nonnegative cap scale. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorScaleLimit
noncomputable section
open Filter Set MeasureTheory SphericalModel SphericalTAPCertificate
open SphericalPureDenominatorFixedCapTransfer SphericalPureCapTailScale
open PureStationarity
open scoped Topology
set_option autoImplicit false

/-- The literal source right-hand limit follows from the lower-tail
estimate and monotonicity in the nonnegative deterministic cap scale. -/
theorem pure_partition_cap_scale_denominator_limit
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (A : ℕ → ℝ) (hAnonneg : ∀ n, 0 ≤ A n) (K : ℝ)
    (hA : Tendsto (fun n : ℕ => capScale (n+3)
      (CSParisiMeasure.variationalValue
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
      (1/(2*x))*A n) atTop (𝓝 K)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    Tendsto (fun η : ℝ => Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
          η*A n}) atTop) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let P (η : ℝ) (n : ℕ) :=
    (disorderLaw (n+3) μ.maxDegree).real
      {J | partition (n+3) β (field (mixtureCoefficients μ) J) < η*A n}
  let f (η : ℝ) := Filter.limsup (P η) atTop
  have hTail := pure_partition_cap_scale_denominator_lower_tail p hp h A K hA
  have hPnonneg (η : ℝ) (n : ℕ) : 0 ≤ P η n := measureReal_nonneg
  have hPbounded (η : ℝ) : IsBoundedUnder (· ≤ ·) atTop (P η) :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hPcobounded (η : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (P η) :=
    isCoboundedUnder_le_of_le atTop (fun n => hPnonneg η n)
  have hf_nonneg (η : ℝ) : 0 ≤ f η := by
    have hZeroCob : IsCoboundedUnder (· ≤ ·) atTop
        (fun _ : ℕ => (0:ℝ)) :=
      isCoboundedUnder_le_of_le atTop (fun _ => le_refl 0)
    have hh := limsup_le_limsup
      (Filter.Eventually.of_forall (fun n => hPnonneg η n))
      hZeroCob (hPbounded η)
    simpa only [f,limsup_const] using hh
  have hf_mono {η₁ η₂ : ℝ} (hη : η₁ ≤ η₂) : f η₁ ≤ f η₂ := by
    apply limsup_le_limsup (h := ?_) (hPcobounded η₁) (hPbounded η₂)
    exact Filter.Eventually.of_forall (fun n =>
      measureReal_mono
        (fun J hJ => lt_of_lt_of_le hJ
          (mul_le_mul_of_nonneg_right hη (hAnonneg n)))
        (by finiteness))
  have hf_small (ε : ℝ) (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ f η ≤ ε := by
    obtain ⟨η,hη,hBound⟩ := hTail ε hε
    exact ⟨η,hη,by simpa only [f,P,μ] using hBound⟩
  change Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0)
  refine tendsto_order.mpr ⟨?_,?_⟩
  · intro z hz
    filter_upwards with η
    exact hz.trans_le (hf_nonneg η)
  · intro z hz
    obtain ⟨η₀,hη₀,hupper⟩ := hf_small (z/2) (half_pos hz)
    filter_upwards [Ioc_mem_nhdsGT hη₀] with η hη
    exact (hf_mono hη.2).trans_lt (lt_of_le_of_lt hupper (by linarith))

end
end SlowEquilibration.SphericalPureDenominatorScaleLimit
