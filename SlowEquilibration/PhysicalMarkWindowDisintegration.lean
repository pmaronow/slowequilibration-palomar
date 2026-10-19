-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMarkedWindows

/-! Exact window restriction of a physical disintegration whose canonical
posterior is supported on every literal mark fiber. Model instances prove
the disintegration and fiber properties from the actual Gaussian maps. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set SphericalMarkedWindows
open scoped ENNReal
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

theorem physical_mark_window_disintegration {Ω Z:Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν:Measure Z) (P0:Measure Ω) (P:Z→Measure Ω) (q:Ω→Z) (hq:Measurable q)
    (D phi:Ω→ℝ≥0∞) (hD:Measurable D) (hphi:Measurable phi)
    (K:Set Z) (hK:MeasurableSet K) (g0 g1:ℝ≥0∞) (pdf:Z→ℝ≥0∞)
    (hFiber:∀ b,∀ᵐ J ∂P b,q J=b)
    (hDis:∀ (f:Ω→ℝ≥0∞),Measurable f → g0*(∫⁻ J,f J ∂P0)=g1*∫⁻ b,pdf b*(∫⁻ J,f J ∂P b) ∂ν) :
    g0*(∫⁻ J,D J*(if q J∈K then phi J else 0) ∂P0)=
      g1*∫⁻ b in K,pdf b*(∫⁻ J,D J*phi J ∂P b) ∂ν:=by
  have hm:Measurable (fun J=>D J*(if q J∈K then phi J else 0)):=
    hD.mul (Measurable.ite (hK.preimage hq) hphi measurable_const)
  rw [hDis _ hm]
  apply congrArg (fun t:ℝ≥0∞=>g1*t)
  calc
    _ = ∫⁻ b,K.indicator (fun b=>pdf b*∫⁻ J,D J*phi J ∂P b) b ∂ν:=by
      apply lintegral_congr
      intro b
      rw [lintegral_window_of_ae_score (P b) q b (hFiber b) K D phi]
      by_cases hb:b∈K
      · simp only [Set.indicator_of_mem hb,ite_eq_left hb]
      · simp only [Set.indicator_of_notMem hb,ite_eq_right hb,mul_zero]
    _ = _:=lintegral_indicator hK _

end
end SlowEquilibration.PairConditionalDeterminantMoments
