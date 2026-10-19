-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePairMarkMarginalIntegral

/-! Exact transfer of a per-mark physical pair intensity upper bound to
the integral on an actual Borel mark window. The source model companions
derive the per-mark bound from their literal posterior and determinants. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open scoped ENNReal
set_option maxHeartbeats 500000

theorem physical_pair_window_integral_transfer {Z Ω:Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω]
    (K:Set Z) (hK:MeasurableSet K) (j:Z→ℝ≥0∞) (hj:Measurable j)
    (P:WithLp 2 (Z×Z)→Measure Ω) (D:Ω→ℝ≥0∞)
    (pdf:WithLp 2 (Z×Z)→ℝ≥0∞) {A g B:ℝ≥0∞} (hA:A≠⊤) (hg:g≠⊤) (hB:B≠⊤)
    (hPoint:∀ b:WithLp 2 (Z×Z),b.fst∈K → b.snd∈K →
      A^2*(g*pdf b*(∫⁻ J,D J ∂P b)) ≤ B*(j b.fst*j b.snd)) :
    A^2*(g*∫⁻ b in {b:WithLp 2 (Z×Z)|b.fst∈K ∧ b.snd∈K},
      pdf b*∫⁻ J,D J ∂P b) ≤ B*((∫⁻ z in K,j z)*(∫⁻ z in K,j z)):=by
  have hSet:MeasurableSet {b:WithLp 2 (Z×Z)|b.fst∈K ∧ b.snd∈K}:=
    (hK.preimage (WithLp.continuous_fst 2 Z Z).measurable).inter
      (hK.preimage (WithLp.continuous_snd 2 Z Z).measurable)
  have hAg:A^2*g≠⊤:=ENNReal.mul_ne_top (ENNReal.pow_ne_top hA) hg
  calc
    _ = ∫⁻ b in {b:WithLp 2 (Z×Z)|b.fst∈K ∧ b.snd∈K},
        A^2*(g*pdf b*(∫⁻ J,D J ∂P b)):=by
      rw [←mul_assoc,←lintegral_const_mul' _ _ hAg]
      apply lintegral_congr
      intro b
      ac_rfl
    _ ≤ ∫⁻ b in {b:WithLp 2 (Z×Z)|b.fst∈K ∧ b.snd∈K},B*(j b.fst*j b.snd):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hSet] with b hb
      exact hPoint b hb.1 hb.2
    _ = B*((∫⁻ z in K,j z)*(∫⁻ z in K,j z)):=by
      rw [lintegral_const_mul' _ _ hB,physical_mark_pair_window_product_integral K hK j hj]

end
end SlowEquilibration.PairConditionalDeterminantMoments
