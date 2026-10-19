-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianSourcePairFactorization
public import SlowEquilibration.SphericalCommonFrameSymmetry
public import SlowEquilibration.PairProductNormalizerTransfer
public import SlowEquilibration.SourcePairIntrinsicDeterminantMoments
public import SlowEquilibration.SphericalWindowGeometry

/-! The source pair determinant ratio under the literal mixed physical
posterior. The two original intrinsic Hessians use a common bulk frame;
their dependence and both adjacent one-point mean normalizations are kept. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open GaussianObservationCoercivity NormalizedPairObservations PairObservationTargets PairObservationSmallOverlap
open SphericalPairCommonFrame SphericalCommonHessianRegression GOEPhysicalPotential
open PhysicalCommonBorderMoments PairSchurExpectation IntrinsicHessianLaw
open GaussianObservationCoercivity GOEClippedResolvent
open SphericalTwoPointCovariance
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem source_mixed_intrinsicDet_product_ratio (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x (tangentFrame x hx))
        (singleMixedObservation c y (tangentFrame y hy))
      let w:=mixedPairTarget (n+3) (n+2) h1 k1 h2 k2
      let m1:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1
      let m2:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k2
      let F:=fun J=>(ConditionedDeterminantMoments.intrinsicDet μ Q x J/m1)*
        (ConditionedDeterminantMoments.intrinsicDet μ Q y J/m2)
      Integrable F (coefficientKernel A w) ∧
        |(∫ J,F J ∂coefficientKernel A w)-1| ≤ C*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)):=by
  obtain ⟨ηf,Cf,hηf,hCf,hFactor⟩:=source_mixed_Schur_normalized_product_factorization μ hQ hnp hd hM hgap
  obtain ⟨η0,δ,hη0,hδ,hCoercive⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  obtain ⟨Cadj,hCadj,hAdj⟩:=source_adjacent_physicalMean_ratio_rate (Z:=M) μ hQ (by omega) hgap
  refine ⟨min ηf (min η0 (1/2)),4*(Cf+3*Cadj),lt_min hηf (lt_min hη0 (by norm_num)),by positivity,?_⟩
  filter_upwards [hFactor,hAdj,
    source_adjacent_physicalMean_lower_eventually (Z:=M) μ hQ (by omega) hgap,
    eventually_ge_atTop (Nat.ceil (4*Cadj^2))] with n hn hAmean hMean hSize
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hr hk1 hk2
  dsimp (config := { failIfUnchanged := false }) only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=Q^2*μ.xi2 Q
  have hb:0<b:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hB:secondCovariance c 1=b:=by rw [secondCovariance_center,secondCovariance_mixture]
  let f:=tangentFrame x hx
  let g:=tangentFrame y hy
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let w:=mixedPairTarget (n+3) (n+2) h1 k1 h2 k2
  let P:=coefficientKernel A w
  have hN:0<n+3:=by omega
  have hrStrict:|overlap x y|<1:=
    (hr.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by norm_num)
  have hrSwap:|overlap y x|<1:=by simpa only [overlap_comm] using hrStrict
  let e:Fin (n+1)→Vector (n+3):=commonFrame hN x y hx hy hrStrict
  let v1:=planeDirection x y
  let v2:=planeDirection y x
  have he:Orthonormal ℝ e:=commonFrame_orthonormal hN x y hx hy hrStrict
  have htanx:∀ i,inner ℝ (e i) x=0:=commonFrame_tangent_left hN x y hx hy hrStrict
  have htany:∀ i,inner ℝ (e i) y=0:=commonFrame_tangent_right hN x y hx hy hrStrict
  have hve1:∀ i,inner ℝ (e i) v1=0:=fun i=>planeDirection_common_inner x y _ (htanx i) (htany i)
  have hve2:∀ i,inner ℝ (e i) v2=0:=fun i=>planeDirection_common_inner y x _ (htany i) (htanx i)
  have hObs:=hCoercive (n+3) (n+2) hN x y hx hy f g
    (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
    (tangentFrame_tangent x hx) (tangentFrame_tangent y hy)
    (hr.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSwap:=coefficientKernel_pair_swap _ _ hObs.2.1 w
  change coefficientKernel (pairHilbert (singleMixedObservation c y g) (singleMixedObservation c x f))
    (mixedPairTarget (n+3) (n+2) h2 k2 h1 k1)=P at hSwap
  have hRad1:=mixed_pair_first_scores_ae hN c x y f g hObs.2.1 h1 k1 h2 k2
  have hObsSwap:=hCoercive (n+3) (n+2) hN y x hy hx g f
    (tangentFrame_orthonormal y hy) (tangentFrame_orthonormal x hx)
    (tangentFrame_tangent y hy) (tangentFrame_tangent x hx)
    (by simpa only [overlap_comm] using hr.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRad2:=mixed_pair_first_scores_ae hN c y x g f hObsSwap.2.1 h2 k2 h1 k1
  rw [hSwap] at hRad2
  let D1:=ConditionedDeterminantMoments.intrinsicDet μ Q x
  let D2:=ConditionedDeterminantMoments.intrinsicDet μ Q y
  let BF1:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v1))
    (actualObservation (commonRowCLM c x e v1)) J
  let BF2:=fun J=>fullBorder (hessianMatrix c y e) k2 (actualObservation (cornerCLM c y v2))
    (actualObservation (commonRowCLM c y e v2)) J
  have hEq1:D1=ᵐ[P] BF1:=by
    filter_upwards [hRad1] with J hJ
    dsimp only [D1,BF1]
    unfold ConditionedDeterminantMoments.intrinsicDet
    exact intrinsic_abs_det_eq_actual_fullBorder c J x y hx hy hrStrict k1 hJ.2
  have hFrame:commonFrame hN y x hy hx hrSwap=e:=(commonFrame_comm hN x y hx hy hrStrict hrSwap).symm
  have hEq2:D2=ᵐ[P] BF2:=by
    filter_upwards [hRad2] with J hJ
    dsimp only [D2,BF2]
    unfold ConditionedDeterminantMoments.intrinsicDet
    rw [intrinsic_abs_det_eq_actual_fullBorder c J y x hy hx hrSwap k2 hJ.2,hFrame]
  have hk1':2*Real.sqrt (secondCovariance c 1)+gap ≤ k1:=by rw [hB];exact hk1
  have hk2':2*Real.sqrt (secondCovariance c 1)+gap ≤ k2:=by rw [hB];exact hk2
  have hFull:=hn (n+2) x y v1 v2 hx hy
    (planeDirection_norm hN x y hx hy hrStrict) (planeDirection_norm hN y x hy hx hrSwap)
    (planeDirection_tangent hN x y hx) (planeDirection_tangent hN y x hy)
    e he htanx htany hve1 hve2 f g
    (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
    (tangentFrame_tangent x hx) (tangentFrame_tangent y hy)
    h1 k1 h2 k2 hh1 hk1M hh2 hk2M (hr.trans (min_le_left _ _)) hk1' hk2'
  dsimp only at hFull
  rw [(show secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1=b from hB)] at hFull
  let a1:=physicalSchurMultiplier b k1*physicalMean n (n+3) b k1
  let a2:=physicalSchurMultiplier b k2*physicalMean n (n+3) b k2
  let m1:=physicalMean (n+1) (n+3) b k1
  let m2:=physicalMean (n+1) (n+3) b k2
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hFullI:Integrable (fun J=>(BF1 J/a1)*(BF2 J/a2)) P:=hFull.1
  have hFullErr:|(∫ J,(BF1 J/a1)*(BF2 J/a2) ∂P)-1| ≤ Cf*ε:=hFull.2
  have hEq:(fun J=>(D1 J/a1)*(D2 J/a2))=ᵐ[P] (fun J=>(BF1 J/a1)*(BF2 J/a2)):=by
    filter_upwards [hEq1,hEq2] with J hJ1 hJ2
    rw [hJ1,hJ2]
  have hI:Integrable (fun J=>(D1 J/a1)*(D2 J/a2)) P:=hFullI.congr hEq.symm
  have hErr:|(∫ J,(D1 J/a1)*(D2 J/a2) ∂P)-1| ≤ Cf*ε:=by rw [integral_congr_ae hEq];exact hFullErr
  have hk1Z:k1 ≤ M:=(le_abs_self _).trans hk1M
  have hk2Z:k2 ≤ M:=(le_abs_self _).trans hk2M
  have hMean1:=hMean k1 hk1 hk1Z
  have hMean2:=hMean k2 hk2 hk2Z
  have ha1:0<a1:=mul_pos (physicalSchurMultiplier_pos hb (by linarith)) hMean1.1
  have ha2:0<a2:=mul_pos (physicalSchurMultiplier_pos hb (by linarith)) hMean2.1
  have hSizeR:4*Cadj^2 ≤ (n+3:ℕ):=
    ((Nat.le_ceil (4*Cadj^2)).trans (show (Nat.ceil (4*Cadj^2):ℝ) ≤ (n:ℝ) by exact_mod_cast hSize)).trans (by norm_cast;omega)
  have hRoot:2*Cadj ≤ Real.sqrt (n+3:ℕ):=(Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith)
  have hSmall:Cadj*(1/Real.sqrt (n+3:ℕ)) ≤ (1/2:ℝ):=by
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hNorm:=dependent_product_normalizer_transfer P D1 D2 ha1.ne' ha2.ne' hMean1.2.1.ne' hMean2.2.1.ne'
    hCadj.le (by positivity) (mul_nonneg hCf.le hε) hSmall
    (by simpa only [mul_one_div] using hAmean k1 hk1 hk1Z)
    (by simpa only [mul_one_div] using hAmean k2 hk2 hk2Z) hI hErr
  refine ⟨hNorm.1,hNorm.2.trans ?_⟩
  dsimp only [ε]
  nlinarith [pow_nonneg (abs_nonneg (overlap x y)) (μ.minDegree-2)]

end
end SlowEquilibration.PairConditionalDeterminantMoments
