-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianFullBorderRealMoments
public import SlowEquilibration.AdjacentPhysicalGOEMean
public import SlowEquilibration.RealMomentNormalizerTransfer
public import SlowEquilibration.PairObservationSmallOverlap
public import SlowEquilibration.ValueObservationSmallOverlap

/-! Every fixed q moment under the source's literal adjacent GOE mean
normalization, on the original mixed/proper-value tensor pair posterior.
Coercivity, ordinary moments and the adjacent mean comparison are proved. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open NormalizedPairObservations GaussianObservationCoercivity SphericalConditionalMatrices
open GOEClippedResolvent GOEPhysicalPotential GOEScaling PhysicalCommonBorderMoments
open PairObservationNormBounds PairObservationSmallOverlap
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- Genuine source adjacent-normalized pair full-border q moments.
No coercivity, determinant moment, or adjacent mean estimate is assumed. -/
theorem source_pair_full_border_mixed_moments (μ : FiniteMixture) {Q g Z M : ℝ}
    (hQ : 0 < Q) (hd : 4 ≤ μ.minDegree) (hnp : μ.minDegree < μ.maxDegree)
    (hg : 0 < g) (hM : 0 ≤ M) (q : ℝ) (hq : 1 ≤ q) :
    ∃ η C:ℝ,0 < η ∧ 0 < C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (ℓ:ℕ) (x y v : Vector (n+3)),‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) →
      ‖v‖=1 → inner ℝ v x=0 →
      ∀ (e:Fin (n+1) → Vector (n+3)),Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) y=0) → (∀ i,inner ℝ (e i) v=0) →
      ∀ (f h:Fin ℓ → Vector (n+3)),Orthonormal ℝ f → Orthonormal ℝ h →
      (∀ i,inner ℝ (f i) x=0) → (∀ i,inner ℝ (h i) y=0) → |overlap x y| ≤ η →
      ∀ (w:WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ)),‖w‖ ≤ M*Real.sqrt (n+3:ℕ) →
      ∀ k:ℝ,2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k → k ≤ Z →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)
      let m:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k
      let D:=fun J=>fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J
      Integrable (fun J=>(D J/m)^q) (coefficientKernel A w) ∧
        (∫ J,(D J/m)^q ∂coefficientKernel A w) ≤ C := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=Q^2*μ.xi2 Q
  have hb : 0 < b:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hc : ∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hB : secondCovariance c 1=b := by rw [secondCovariance_center,secondCovariance_mixture]
  have hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val:=center_degree_four hd Q
  let ρ:=g/(4*Real.sqrt b)
  have hρ : 0 < ρ:=by dsimp only [ρ];positivity
  have hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1)) := by
    rw [hB]
    dsimp only [ρ]
    apply div_le_div_of_nonneg_left hg.le (by positivity)
    linarith [Real.sqrt_pos.mpr hb]
  obtain ⟨η0,δ,hη0,hδ,hCoercive⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  let η:=min η0 1
  let B0:=1+fullBorderIntegerBound (Nat.ceil q) b g ρ Z (7*profileBound c*M/δ) (profileBound c*M/δ)
  let L:=2/Real.sqrt b
  let C:=L^q*B0
  have hL : 0 < L:=by dsimp only [L];positivity
  have hB0 : 0 < B0 := by dsimp only [B0,fullBorderIntegerBound];positivity
  refine ⟨η,C,lt_min hη0 (by norm_num),mul_pos (Real.rpow_pos_of_pos hL q) hB0,?_⟩
  filter_upwards [actual_common_border_mixed_real_moment_eventually q hq (Z:=Z) c hc (hB.symm ▸ hb)
    hdeg hg hρ hρg hδ hM,
    source_adjacent_physicalMean_lower_eventually (Z:=Z) μ hQ (by omega : 3 ≤ μ.minDegree) hg] with n hn hMean
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hf hh hfTan hhTan hr w hw k hk hkZ
  dsimp only
  have hCo:=hCoercive (n+3) ℓ (by omega) x y hx hy f h hf hh hfTan hhTan (hr.trans (min_le_left _ _))
  have hk' : 2*Real.sqrt (secondCovariance c 1)+g ≤ k:=by rwa [hB]
  have hBase:=hn ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh
    (hr.trans (min_le_right _ _)) hCo.2.1 hCo.2.2 w hw k hk' hkZ
  have hMeanBounds:=hMean k hk hkZ
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)
  let D:=fun J:Disorder (n+3) μ.maxDegree=>fullBorder (hessianMatrix c x e) k
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J
  have hDM : Measurable D:=fullBorder_measurable (tensor_hessianMatrix_measurable c x e) k
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)
  have hD0 (J) : 0 ≤ D J:=abs_nonneg _
  have hI : Integrable (fun J=>(D J/physicalMean n (n+3) b k)^q) (coefficientKernel A w) := by
    simpa only [hB] using hBase.2.1
  have hBound : (∫ J,(D J/physicalMean n (n+3) b k)^q ∂coefficientKernel A w) ≤ B0 := by
    simpa only [hB,B0] using hBase.2.2
  exact NonnegativeRealMoment.real_moment_normalizer_transfer (coefficientKernel A w) D hDM hD0
    hMeanBounds.1 hMeanBounds.2.1 hL.le (by linarith : 0 ≤ q) hMeanBounds.2.2 hI hBound

/-- Genuine source adjacent-normalized pair full-border q moments.
No coercivity, determinant moment, or adjacent mean estimate is assumed. -/
theorem source_pair_full_border_value_moments (μ : FiniteMixture) {Q g Z M : ℝ}
    (hQ : 0 < Q) (hd : 4 ≤ μ.minDegree)
    (hg : 0 < g) (hM : 0 ≤ M) (q : ℝ) (hq : 1 ≤ q) :
    ∃ η C:ℝ,0 < η ∧ 0 < C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (ℓ:ℕ) (x y v : Vector (n+3)),‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) →
      ‖v‖=1 → inner ℝ v x=0 →
      ∀ (e:Fin (n+1) → Vector (n+3)),Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) y=0) → (∀ i,inner ℝ (e i) v=0) →
      ∀ (f h:Fin ℓ → Vector (n+3)),Orthonormal ℝ f → Orthonormal ℝ h →
      (∀ i,inner ℝ (f i) x=0) → (∀ i,inner ℝ (h i) y=0) → |overlap x y| ≤ η →
      ∀ (w:WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ)),‖w‖ ≤ M*Real.sqrt (n+3:ℕ) →
      ∀ k:ℝ,2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k → k ≤ Z →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)
      let m:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k
      let D:=fun J=>fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J
      Integrable (fun J=>(D J/m)^q) (coefficientKernel A w) ∧
        (∫ J,(D J/m)^q ∂coefficientKernel A w) ≤ C := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=Q^2*μ.xi2 Q
  have hb : 0 < b:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hc : ∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hB : secondCovariance c 1=b := by rw [secondCovariance_center,secondCovariance_mixture]
  have hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val:=center_degree_four hd Q
  let ρ:=g/(4*Real.sqrt b)
  have hρ : 0 < ρ:=by dsimp only [ρ];positivity
  have hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1)) := by
    rw [hB]
    dsimp only [ρ]
    apply div_le_div_of_nonneg_left hg.le (by positivity)
    linarith [Real.sqrt_pos.mpr hb]
  obtain ⟨η0,δ,hη0,hδ,hCoercive⟩:=uniform_value_pair_nondegenerate μ hQ hd
  let η:=min η0 1
  let B0:=1+fullBorderIntegerBound (Nat.ceil q) b g ρ Z (7*profileBound c*M/δ) (profileBound c*M/δ)
  let L:=2/Real.sqrt b
  let C:=L^q*B0
  have hL : 0 < L:=by dsimp only [L];positivity
  have hB0 : 0 < B0 := by dsimp only [B0,fullBorderIntegerBound];positivity
  refine ⟨η,C,lt_min hη0 (by norm_num),mul_pos (Real.rpow_pos_of_pos hL q) hB0,?_⟩
  filter_upwards [actual_common_border_value_real_moment_eventually q hq (Z:=Z) c hc (hB.symm ▸ hb)
    hdeg hg hρ hρg hδ hM,
    source_adjacent_physicalMean_lower_eventually (Z:=Z) μ hQ (by omega : 3 ≤ μ.minDegree) hg] with n hn hMean
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hf hh hfTan hhTan hr w hw k hk hkZ
  dsimp only
  have hCo:=hCoercive (n+3) ℓ (by omega) x y hx hy f h hf hh hfTan hhTan (hr.trans (min_le_left _ _))
  have hk' : 2*Real.sqrt (secondCovariance c 1)+g ≤ k:=by rwa [hB]
  have hBase:=hn ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh
    (hr.trans (min_le_right _ _)) hCo.2.1 hCo.2.2 w hw k hk' hkZ
  have hMeanBounds:=hMean k hk hkZ
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)
  let D:=fun J:Disorder (n+3) μ.maxDegree=>fullBorder (hessianMatrix c x e) k
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J
  have hDM : Measurable D:=fullBorder_measurable (tensor_hessianMatrix_measurable c x e) k
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)
  have hD0 (J) : 0 ≤ D J:=abs_nonneg _
  have hI : Integrable (fun J=>(D J/physicalMean n (n+3) b k)^q) (coefficientKernel A w) := by
    simpa only [hB] using hBase.2.1
  have hBound : (∫ J,(D J/physicalMean n (n+3) b k)^q ∂coefficientKernel A w) ≤ B0 := by
    simpa only [hB,B0] using hBase.2.2
  exact NonnegativeRealMoment.real_moment_normalizer_transfer (coefficientKernel A w) D hDM hD0
    hMeanBounds.1 hMeanBounds.2.1 hL.le (by linarith : 0 ≤ q) hMeanBounds.2.2 hI hBound

end
end SlowEquilibration.SphericalCommonHessianRegression
