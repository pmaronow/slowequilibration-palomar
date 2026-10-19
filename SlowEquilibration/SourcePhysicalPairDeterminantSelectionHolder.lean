-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionFailureRates
public import SlowEquilibration.GOEMaximumDeterminant

/-! Actual determinant-weighted selection loss. The own ordinary
determinant moment and the literal raw-posterior failure are proved
inputs, giving a vanishing relative loss uniformly in compact marks. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity
open GOEMaximumDeterminant
open scoped ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] Classical.propDecidable

theorem sourceDeterminant_retained_weight_lower {Ω:Type*} [MeasurableSpace Ω]
    (ν:Measure Ω) [IsProbabilityMeasure ν] (D:Ω→ℝ) (B:Set Ω) (hB:MeasurableSet B)
    (hD:Integrable D ν) (hDn:∀ᵐ x ∂ν,0 ≤ D x) (hm:0<∫ x,D x ∂ν)
    {C q:ℝ} (hM:Integrable (fun x=>(D x/(∫ y,D y ∂ν))^(2:ℝ)) ν)
    (hMC:(∫ x,(D x/(∫ y,D y ∂ν))^(2:ℝ) ∂ν) ≤ C)
    (hq:ν.real Bᶜ ≤ q) (herr:Real.sqrt C*Real.sqrt q ≤ 1) :
    ENNReal.ofReal (1-Real.sqrt C*Real.sqrt q)*(∫⁻ x,ENNReal.ofReal (D x) ∂ν) ≤
      ∫⁻ x,ENNReal.ofReal (D x)*B.indicator (fun _=>1) x ∂ν:=by
  have hloss:=determinant_event_holder ν D hD hDn hm Bᶜ hB.compl hM hMC hq
  have hloss':(∫ x in Bᶜ,D x ∂ν) ≤ (Real.sqrt C*Real.sqrt q)*(∫ x,D x ∂ν):=
    (div_le_iff₀ hm).mp hloss
  have hpartition:=integral_add_compl hB hD
  have hgood:(1-Real.sqrt C*Real.sqrt q)*(∫ x,D x ∂ν) ≤ ∫ x in B,D x ∂ν:=by
    linarith
  rw [←ofReal_integral_eq_lintegral_ofReal hD hDn,
    ←ENNReal.ofReal_mul (sub_nonneg.mpr herr)]
  refine (ENNReal.ofReal_le_ofReal hgood).trans_eq ?_
  calc
    ENNReal.ofReal (∫ x in B,D x ∂ν)=∫⁻ x in B,ENNReal.ofReal (D x) ∂ν:=
      ofReal_integral_eq_lintegral_ofReal hD.restrict (ae_restrict_of_ae hDn)
    _ = ∫⁻ x,B.indicator (fun x=>ENNReal.ofReal (D x)) x ∂ν:=(lintegral_indicator hB _).symm
    _ = _:=by
      apply lintegral_congr
      intro x
      by_cases hx:x ∈ B
      · simp only [Set.indicator_of_mem hx,mul_one]
      · simp only [Set.indicator_of_notMem hx,mul_zero]

end
end SlowEquilibration.PairConditionalDeterminantMoments
