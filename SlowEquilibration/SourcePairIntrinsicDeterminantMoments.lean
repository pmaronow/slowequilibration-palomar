-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePairFullBorderMoments
public import SlowEquilibration.SphericalGeometricIntrinsicBorder
public import SlowEquilibration.PairObservationFiber

/-! Source physical mixed pair intrinsic determinant q moments with the
literal adjacent GOE mean normalization. All source targets, geometric
frames, coercivity and radial-fiber facts are derived inside the consumer. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open NormalizedPairObservations GaussianObservationCoercivity SphericalConditionalMatrices
open SphericalPairCommonFrame SphericalCommonHessianRegression PairObservationTargets PairObservationSmallOverlap
open GOEClippedResolvent GOEPhysicalPotential GOEScaling PhysicalCommonBorderMoments
open IntrinsicHessianLaw
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The actual full intrinsic source determinant has bounded every fixed
q moment under true two-point mixed physical marks, normalized by literal
μ_{N−1,N}. Constants and overlap radius precede dimension and all marks. -/
theorem source_mixed_pair_intrinsicDet_q_moments (μ : FiniteMixture) {Q g Z M : ℝ}
    (hQ : 0 < Q) (hd : 4 ≤ μ.minDegree) (hnp : μ.minDegree < μ.maxDegree)
    (hg : 0 < g) (hM : 0 ≤ M) (q : ℝ) (hq : 1 ≤ q) :
    ∃ η C:ℝ,0 < η ∧ 0 < C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ)),
      ∀ h1 k1 h2 k2:ℝ,|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k1 → k1 ≤ Z →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x (tangentFrame x hx))
        (singleMixedObservation c y (tangentFrame y hy))
      let w:=mixedPairTarget (n+3) (n+2) h1 k1 h2 k2
      let m:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1
      Integrable (fun J=>(ConditionedDeterminantMoments.intrinsicDet μ Q x J/m)^q) (coefficientKernel A w) ∧
        (∫ J,(ConditionedDeterminantMoments.intrinsicDet μ Q x J/m)^q ∂coefficientKernel A w) ≤ C := by
  obtain ⟨η1,C,hη1,hC,hAll⟩:=source_pair_full_border_mixed_moments (M:=4*M) μ hQ hd hnp hg (by positivity) q hq
  obtain ⟨η0,δ,hη0,hδ,hCoercive⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  let η:=min η1 (min η0 (1/2))
  refine ⟨η,C,lt_min hη1 (lt_min hη0 (by norm_num)),hC,?_⟩
  filter_upwards [hAll] with n hn
  intro x y hx hy h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hk hkZ
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let f:=tangentFrame x hx
  let h:=tangentFrame y hy
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)
  let w:=mixedPairTarget (n+3) (n+2) h1 k1 h2 k2
  let m:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1
  have hr0 : |overlap x y| ≤ η0:=hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrStrict : |overlap x y| < 1 := (hr.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by norm_num)
  have hN : 0 < n+3:=by omega
  let e : Fin (n+1) → Vector (n+3):=commonFrame hN x y hx hy hrStrict
  let v:=planeDirection x y
  have he : Orthonormal ℝ e:=commonFrame_orthonormal hN x y hx hy hrStrict
  have htanx : ∀ i,inner ℝ (e i) x=0:=commonFrame_tangent_left hN x y hx hy hrStrict
  have htany : ∀ i,inner ℝ (e i) y=0:=commonFrame_tangent_right hN x y hx hy hrStrict
  have hve : ∀ i,inner ℝ (e i) v=0:=fun i=>planeDirection_common_inner x y _ (htanx i) (htany i)
  have hA:=hCoercive (n+3) (n+2) hN x y hx hy f h
    (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
    (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr0
  have hFull:=hn (n+2) x y v hx hy (planeDirection_norm hN x y hx hy hrStrict)
    (planeDirection_tangent hN x y hx) e he htanx htany hve f h
    (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
    (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) (hr.trans (min_le_left _ _)) w
    (mixedPairTarget_norm_le (n+3) (n+2) hh1 hk1 hh2 hk2) k1 hk hkZ
  have hRad:=mixed_pair_first_scores_ae hN c x y f h hA.2.1 h1 k1 h2 k2
  have hEq : (fun J:Disorder (n+3) μ.maxDegree=>(ConditionedDeterminantMoments.intrinsicDet μ Q x J/m)^q)=ᵐ[coefficientKernel A w]
      (fun J=>(fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
        (actualObservation (commonRowCLM c x e v)) J/m)^q) := by
    filter_upwards [hRad] with J hJ
    unfold ConditionedDeterminantMoments.intrinsicDet
    rw [intrinsic_abs_det_eq_actual_fullBorder (n:=n) c J x y hx hy hrStrict k1 hJ.2]
  refine ⟨hFull.1.congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq]
  exact hFull.2

end
end SlowEquilibration.PairConditionalDeterminantMoments
