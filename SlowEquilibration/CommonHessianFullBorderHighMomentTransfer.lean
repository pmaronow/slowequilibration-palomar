-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianBorderHighMomentTransfer

/-! Genuine every-real-q raw full-border error from the actual clipped
Schur scalar and the true matrix spectral gap. -/
@[expose] public section
namespace SlowEquilibration.PhysicalCommonBorderMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Set Matrix
open BorderSchurExpectation BorderClippedSchurIdentity GOEPhysicalGapEvent
open GOEClippedResolvent GOERawMoments GOEPhysicalPotential
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {Ω:Type*} [MeasurableSpace Ω] {P:Measure Ω}

/-- True absolute determinant q-error on its original probability space.
The spectral-gap conclusion is proved from the literal matrix and row. -/
theorem normalized_full_border_schur_q_error [IsProbabilityMeasure P]
    {n N:ℕ} {b k κ:ℝ} (hκ:0<κ)
    (W:Ω→Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hW:Measurable W)
    (hSym:∀ x,(W x).IsHermitian)
    (hLaw:HasLaw W (SphericalGaussianJet.goeLaw (n+1) N b) P)
    (a:Ω→ℝ) (u:Ω→EuclideanSpace ℝ (Fin (n+1))) (ha:Measurable a) (hu:Measurable u)
    (hm:0<physicalMean n N b k) (s q:ℝ) (hq:0 ≤ q)
    (hD2q:Integrable (fun x=>|fullBorder W k a u x/physicalMean n N b k|^(2*q)) P)
    (hB2q:Integrable (fun x=>|matrixAbsoluteDet n k (W x)/physicalMean n N b k|^(2*q)) P)
    (hT2q:Integrable (fun x=>|clippedSchur W k κ a u x-s|^(2*q)) P)
    (hT:Measurable (clippedSchur W k κ a u)) :
    let m:=physicalMean n N b k
    let B:=fun x=>matrixAbsoluteDet n k (W x)/m
    let D:=fun x=>fullBorder W k a u x/m
    let T:=fun x=>clippedSchur W k κ a u x-s
    Integrable (fun x=>|D x-|s| *B x|^q) P ∧
      (∫ x,|D x-|s| *B x|^q ∂P) ≤
        Real.sqrt (∫ x,|B x|^(2*q) ∂P)*Real.sqrt (∫ x,|T x|^(2*q) ∂P)+
        (2:ℝ)^q*(Real.sqrt (∫ x,|D x|^(2*q) ∂P)+
          |s|^q*Real.sqrt (∫ x,|B x|^(2*q) ∂P))*
            Real.sqrt ((SphericalGaussianJet.goeLaw (n+1) N b).real (gapEvent n k κ)ᶜ):=by
  dsimp only
  let m:=physicalMean n N b k
  let D:=fun x=>fullBorder W k a u x/m
  let B:=fun x=>matrixAbsoluteDet n k (W x)/m
  let T:=clippedSchur W k κ a u
  let G:=W ⁻¹' gapEvent n k κ
  have hG:MeasurableSet G:=(gapEvent_measurable n k κ).preimage hW
  have hDM:Measurable D:=(fullBorder_measurable hW k ha hu).div_const m
  have hBM:Measurable B:=((matrixAbsoluteDet_measurable n k).comp hW).div_const m
  have hgood:∀ᵐ x ∂P,x∈G → |D x-|s| *B x| ≤ |B x| *|T x-s|:=by
    filter_upwards [] with x
    intro hx
    have hgap:‖(Matrix.toEuclideanCLM (n:=Fin (n+1)) (𝕜:=ℝ)) (W x)‖ ≤ k-κ:=hx
    have hp:=border_abs_error_of_norm_gap (W x) (hSym x) k hκ hgap (k-a x) s (u x)
    have hleft:|D x-|s| *B x|=|fullBorder W k a u x-|s| *matrixAbsoluteDet n k (W x)|/m:=by
      dsimp only [D,B]
      rw [←mul_div_assoc,←sub_div,abs_div,abs_of_pos hm]
    have hB0:0 ≤ B x:=div_nonneg (abs_nonneg _) hm.le
    rw [hleft,abs_of_nonneg hB0]
    exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by
      dsimp only [B,T,clippedSchur,m,matrixAbsoluteDet]
      ring)
  have hprob:P.real Gᶜ=(SphericalGaussianJet.goeLaw (n+1) N b).real (gapEvent n k κ)ᶜ:=by
    rw [←hLaw.map_eq]
    simp only [Measure.real]
    rw [Measure.map_apply hW (gapEvent_measurable n k κ).compl]
    rfl
  have hE:=integral_q_error_of_good_event P D B T hDM hBM hT s q hq
    hD2q hB2q hT2q G hG hgood
  rwa [hprob] at hE

end
end SlowEquilibration.PhysicalCommonBorderMoments
