-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianSourceMixedSchurHighMoments
public import SlowEquilibration.CommonHessianSourceValueSchurHighMoments
public import SlowEquilibration.CommonHessianFullBorderRealMoments
public import SlowEquilibration.CommonHessianFullBorderHighMomentRates

/-! Source physical original-posterior all-q full/raw common determinant
error. True Schur, full-border moments, raw GOE moments and rare gap law
are all derived internally before dimension, physical marks and frames. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open GaussianObservationCoercivity NormalizedPairObservations PairObservationNormBounds
open PairObservationTargets PairObservationSmallOverlap GaussianQuadraticVariance
open GOEClippedResolvent GOEScaling GOEPhysicalPotential GOERawMoments
open PhysicalCommonBorderMoments BorderSchurExpectation BorderClippedSchurIdentity
open GOEPhysicalGapEvent SchurDimensionRates
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- Genuine source mixed full-border q error with its exact physical
bulk mean; no determinant approximation or source rate is assumed. -/
theorem source_mixed_full_border_q_error (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap)
    (q:ℝ) (hq:1 ≤ q) :
    ∃ η Cq:ℝ,0<η ∧ 0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 k1 h2 k2:ℝ), |h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
      let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
      let b:=secondCovariance c 1
      let m:=physicalMean n (n+3) b k1
      let s:=physicalSchurMultiplier b k1
      let D:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
        (actualObservation (commonRowCLM c x e v)) J/m
      let B:=fun J=>matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m
      Integrable (fun J=>|D J-s*B J|^q) (coefficientKernel A w) ∧
      (∫ J,|D J-s*B J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ))^q:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hc:∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hdeg:∀ p,c p≠0 → 4 ≤ p.val.val:=center_degree_four hd Q
  have hb:0<b:=by
    dsimp only [b,c]
    rw [secondCovariance_center,secondCovariance_mixture]
    exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  let ρ:=gap/(4*Real.sqrt b)
  have hρ:0<ρ:=by dsimp only [ρ];positivity
  have hρg:ρ ≤ gap/(2*Real.sqrt b):=by dsimp only [ρ];gcongr <;> norm_num
  have hρg':ρ ≤ (gap/Real.sqrt b)/2:=by convert hρg using 1 <;> ring
  have hq0:0 ≤ q:=by linarith
  have hq2:1 ≤ 2*q:=by linarith
  obtain ⟨η0,δ,hη0,hδ,hObs⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  obtain ⟨ηs,Ks,hηs,hKs,hSchur⟩:=source_mixed_clipped_schur_q_rate μ hQ hnp hd hM hgap hρ hρg' (2*q) (by positivity)
  let KD:=1+fullBorderIntegerBound (Nat.ceil (2*q)) b gap ρ M
    (7*profileBound c*(4*M)/δ) (profileBound c*(4*M)/δ)
  let KB:=(2:ℝ)^(2*q)*Real.exp (4*b*(2*q)^2/gap^2)
  let K:=Real.sqrt KB*Real.sqrt Ks+(2:ℝ)^q*(Real.sqrt KD+M^q*Real.sqrt KB)*gapMomentConstant (gap/Real.sqrt b) q
  have hKD:0 ≤ KD:=by dsimp only [KD,fullBorderIntegerBound];positivity
  have hKB:0 ≤ KB:=by dsimp only [KB];positivity
  have hK:0 ≤ K:=by dsimp only [K,gapMomentConstant];positivity
  refine ⟨min η0 (min ηs 1),1+K,lt_min hη0 (lt_min hηs (by norm_num)),by positivity,?_⟩
  filter_upwards [hSchur,actual_common_border_mixed_real_moment_eventually (2*q) hq2 (Z:=M) c hc hb hdeg
    hgap hρ hρg hδ (show 0 ≤ 4*M by positivity),
    GOESharpMoments.goe_determinant_moments_eventually hb hgap,
    physical_gap_failure_eventually hb hgap hρ hρg] with n hS hFullAll hRawAll hGapAll
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hk
  dsimp only
  have hr0:|overlap x y| ≤ η0:=hr.trans (min_le_left _ _)
  have hrs:|overlap x y| ≤ ηs:=hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrOne:|overlap x y| ≤ 1:=hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hObs0:=hObs (n+3) ℓ (by omega) x y hx hy f g hf hg hftan hgtan hr0
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
  let P:=coefficientKernel A w
  let m:=physicalMean n (n+3) b k1
  let κ:=scaleFactor n (n+3) b*ρ
  let W:=hessianMatrix c x e
  let a:=actualObservation (cornerCLM c x v)
  let u:=actualObservation (commonRowCLM c x e v)
  let D:=fun J=>fullBorder W k1 a u J/m
  let B:=fun J=>matrixAbsoluteDet n k1 (W J)/m
  let T:=actualClippedSchurFactor c x e v k1 κ
  let s:=physicalSchurMultiplier b k1
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hWtarget:‖w‖ ≤ (4*M)*Real.sqrt (n+3:ℕ):=mixedPairTarget_norm_le _ _ hh1 hk1 hh2 hk2
  have hkM:k1 ≤ M:=(le_abs_self _).trans hk1
  have hFull:=hFullAll ℓ x y v hx hy hv hvtan e he htanx htany hve f g hg hrOne
    hObs0.2.1 hObs0.2.2 w hWtarget k1 hk hkM
  have hm:0 < m:=hFull.1
  have hD0 (J):0 ≤ D J:=div_nonneg (abs_nonneg _) hm.le
  have hB0 (J):0 ≤ B J:=div_nonneg (abs_nonneg _) hm.le
  have hDI:Integrable (fun J=>|D J|^(2*q)) P:=by simpa only [abs_of_nonneg (hD0 _)] using hFull.2.1
  have hDM:(∫ J,|D J|^(2*q) ∂P) ≤ KD:=by simpa only [abs_of_nonneg (hD0 _)] using hFull.2.2
  have hRaw:=hRawAll (n+3) (by omega) k1 hk
  have hBmom:=hRaw.2.2 (2*q) (by positivity)
  have hLaw:=posterior_common_matrix_mixed_hasLaw (by omega : 0<n+3) c hc
    (fun p hp=>le_trans (by omega : 3 ≤ 4) (hdeg p hp)) x y hx e he htanx htany f g w
  have hBI0:Integrable (fun J=>B J^(2*q)) P:=by
    simpa only [Function.comp_def,B,W,m,b,physicalMean,
      GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet] using hLaw.integrable_fun_comp hBmom.1
  have hBI:Integrable (fun J=>|B J|^(2*q)) P:=by
    simpa only [abs_of_nonneg (hB0 _)] using hBI0
  have hBM:(∫ J,|B J|^(2*q) ∂P) ≤ KB:=by
    have hh:=hLaw.integral_comp (((matrixAbsoluteDet_measurable n k1).div_const m).pow_const (2*q)).aestronglyMeasurable
    simp only [Function.comp_def] at hh
    simp only [abs_of_nonneg (hB0 _)]
    change (∫ J,B J^(2*q) ∂P) ≤ _
    rw [hh]
    exact hBmom.2
  have hSmom:=hS ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1 hh2 hk2 hrs hk
  have hTI:Integrable (fun J=>|T J-s|^(2*q)) P:=hSmom.1
  have hTM:(∫ J,|T J-s|^(2*q) ∂P) ≤ Ks*ε^(2*q):=hSmom.2
  have hWM:Measurable W:=tensor_hessianMatrix_measurable c x e
  have haM:Measurable a:=actual_linearObservation_measurable _
  have huM:Measurable u:=actual_linearObservation_measurable _
  have hDMb:Measurable D:=(fullBorder_measurable hWM k1 haM huM).div_const m
  have hBMb:Measurable B:=((matrixAbsoluteDet_measurable n k1).comp hWM).div_const m
  have hκ:0<κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hTMb:Measurable T:=actualClippedSchurFactor_measurable c x e v k1 hκ
  have hSym (J:Disorder (n+3) μ.maxDegree):(W J).IsHermitian:=by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial,W,hessianMatrix] using hessianEntry_symm c x e j i J
  let G:=W ⁻¹' gapEvent n k1 κ
  have hG:MeasurableSet G:=(gapEvent_measurable n k1 κ).preimage hWM
  have hgood:∀ᵐ J ∂P,J∈G → |D J-|s| * B J| ≤ |B J| * |T J-s|:=by
    filter_upwards [] with J
    intro hJ
    have hp:=border_abs_error_of_norm_gap (W J) (hSym J) k1 hκ hJ (k1-a J) s (u J)
    have hleft:|D J-|s| * B J|=|fullBorder W k1 a u J-|s| * matrixAbsoluteDet n k1 (W J)|/m:=by
      dsimp only [D,B]
      rw [←mul_div_assoc,←sub_div,abs_div,abs_of_pos hm]
    rw [hleft,abs_of_nonneg (hB0 J)]
    exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by
      dsimp only [B,T,actualClippedSchurFactor,m,matrixAbsoluteDet,W,a,u]
      ring)
  have hProb:P.real Gᶜ=(goeLaw (n+1) (n+3) b).real (gapEvent n k1 κ)ᶜ:=by
    rw [←hLaw.map_eq]
    simp only [Measure.real]
    rw [Measure.map_apply hWM (gapEvent_measurable n k1 κ).compl]
    rfl
  have hGap:P.real Gᶜ ≤ Real.exp (-(n+1:ℝ)*(gap/Real.sqrt b)^2/(16*Real.pi^2)):=by
    rw [hProb]
    exact hGapAll (n+3) (by omega) k1 hk
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hInv:1/Real.sqrt (n+3:ℕ) ≤ ε:=le_add_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
  have hRate:=q_error_good_event_rate P D B T hDMb hBMb hTMb s q hq0 hDI hBI hTI G hG hgood n
    (div_pos hgap (Real.sqrt_pos.mpr hb)) hε hInv hKD hKB hKs.le hDM hBM hTM hGap
  have hs:0<s:=physicalSchurMultiplier_pos hb (by linarith)
  have hsM:s ≤ M:=(physicalSchurMultiplier_bounds hb (by linarith)).2.trans hkM
  simp only [abs_of_pos hs] at hRate
  refine ⟨hRate.1,hRate.2.trans ?_⟩
  have hsQ:s^q ≤ M^q:=Real.rpow_le_rpow hs.le hsM hq0
  have hGapC:0 ≤ gapMomentConstant (gap/Real.sqrt b) q:=by unfold gapMomentConstant;positivity
  calc
    _ ≤ K*ε^q:=by dsimp only [K];gcongr
    _ ≤ (1+K)*ε^q:=mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hε q)

/-- Genuine source value full-border q error with its exact physical
bulk mean; no determinant approximation or source rate is assumed. -/
theorem source_value_full_border_q_error (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap)
    (q:ℝ) (hq:1 ≤ q) :
    ∃ η Cq:ℝ,0<η ∧ 0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 h2 k1:ℝ), |h1| ≤ M → |h2| ≤ M → |k1| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
      let w:=valuePairTarget (n+3) ℓ h1 h2
      let b:=secondCovariance c 1
      let m:=physicalMean n (n+3) b k1
      let s:=physicalSchurMultiplier b k1
      let D:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
        (actualObservation (commonRowCLM c x e v)) J/m
      let B:=fun J=>matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m
      Integrable (fun J=>|D J-s*B J|^q) (coefficientKernel A w) ∧
      (∫ J,|D J-s*B J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ))^q:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hc:∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hdeg:∀ p,c p≠0 → 4 ≤ p.val.val:=center_degree_four hd Q
  have hb:0<b:=by
    dsimp only [b,c]
    rw [secondCovariance_center,secondCovariance_mixture]
    exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  let ρ:=gap/(4*Real.sqrt b)
  have hρ:0<ρ:=by dsimp only [ρ];positivity
  have hρg:ρ ≤ gap/(2*Real.sqrt b):=by dsimp only [ρ];gcongr <;> norm_num
  have hρg':ρ ≤ (gap/Real.sqrt b)/2:=by convert hρg using 1 <;> ring
  have hq0:0 ≤ q:=by linarith
  have hq2:1 ≤ 2*q:=by linarith
  obtain ⟨η0,δ,hη0,hδ,hObs⟩:=uniform_value_pair_nondegenerate μ hQ hd
  obtain ⟨ηs,Ks,hηs,hKs,hSchur⟩:=source_value_clipped_schur_q_rate μ hQ hd hM hgap hρ hρg' (2*q) (by positivity)
  let KD:=1+fullBorderIntegerBound (Nat.ceil (2*q)) b gap ρ M
    (7*profileBound c*(2*M)/δ) (profileBound c*(2*M)/δ)
  let KB:=(2:ℝ)^(2*q)*Real.exp (4*b*(2*q)^2/gap^2)
  let K:=Real.sqrt KB*Real.sqrt Ks+(2:ℝ)^q*(Real.sqrt KD+M^q*Real.sqrt KB)*gapMomentConstant (gap/Real.sqrt b) q
  have hKD:0 ≤ KD:=by dsimp only [KD,fullBorderIntegerBound];positivity
  have hKB:0 ≤ KB:=by dsimp only [KB];positivity
  have hK:0 ≤ K:=by dsimp only [K,gapMomentConstant];positivity
  refine ⟨min η0 (min ηs 1),1+K,lt_min hη0 (lt_min hηs (by norm_num)),by positivity,?_⟩
  filter_upwards [hSchur,actual_common_border_value_real_moment_eventually (2*q) hq2 (Z:=M) c hc hb hdeg
    hgap hρ hρg hδ (show 0 ≤ 2*M by positivity),
    GOESharpMoments.goe_determinant_moments_eventually hb hgap,
    physical_gap_failure_eventually hb hgap hρ hρg] with n hS hFullAll hRawAll hGapAll
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 h2 k1 hh1 hh2 hk1 hr hk
  dsimp only
  have hr0:|overlap x y| ≤ η0:=hr.trans (min_le_left _ _)
  have hrs:|overlap x y| ≤ ηs:=hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrOne:|overlap x y| ≤ 1:=hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hObs0:=hObs (n+3) ℓ (by omega) x y hx hy f g hf hg hftan hgtan hr0
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) ℓ h1 h2
  let P:=coefficientKernel A w
  let m:=physicalMean n (n+3) b k1
  let κ:=scaleFactor n (n+3) b*ρ
  let W:=hessianMatrix c x e
  let a:=actualObservation (cornerCLM c x v)
  let u:=actualObservation (commonRowCLM c x e v)
  let D:=fun J=>fullBorder W k1 a u J/m
  let B:=fun J=>matrixAbsoluteDet n k1 (W J)/m
  let T:=actualClippedSchurFactor c x e v k1 κ
  let s:=physicalSchurMultiplier b k1
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hWtarget:‖w‖ ≤ (2*M)*Real.sqrt (n+3:ℕ):=valuePairTarget_norm_le _ _ hh1 hh2
  have hkM:k1 ≤ M:=(le_abs_self _).trans hk1
  have hFull:=hFullAll ℓ x y v hx hy hv hvtan e he htanx htany hve f g hg hrOne
    hObs0.2.1 hObs0.2.2 w hWtarget k1 hk hkM
  have hm:0 < m:=hFull.1
  have hD0 (J):0 ≤ D J:=div_nonneg (abs_nonneg _) hm.le
  have hB0 (J):0 ≤ B J:=div_nonneg (abs_nonneg _) hm.le
  have hDI:Integrable (fun J=>|D J|^(2*q)) P:=by simpa only [abs_of_nonneg (hD0 _)] using hFull.2.1
  have hDM:(∫ J,|D J|^(2*q) ∂P) ≤ KD:=by simpa only [abs_of_nonneg (hD0 _)] using hFull.2.2
  have hRaw:=hRawAll (n+3) (by omega) k1 hk
  have hBmom:=hRaw.2.2 (2*q) (by positivity)
  have hLaw:=posterior_common_matrix_value_hasLaw (by omega : 0<n+3) c hc
    (fun p hp=>le_trans (by omega : 3 ≤ 4) (hdeg p hp)) x y hx e he htanx htany f g w
  have hBI0:Integrable (fun J=>B J^(2*q)) P:=by
    simpa only [Function.comp_def,B,W,m,b,physicalMean,
      GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet] using hLaw.integrable_fun_comp hBmom.1
  have hBI:Integrable (fun J=>|B J|^(2*q)) P:=by
    simpa only [abs_of_nonneg (hB0 _)] using hBI0
  have hBM:(∫ J,|B J|^(2*q) ∂P) ≤ KB:=by
    have hh:=hLaw.integral_comp (((matrixAbsoluteDet_measurable n k1).div_const m).pow_const (2*q)).aestronglyMeasurable
    simp only [Function.comp_def] at hh
    simp only [abs_of_nonneg (hB0 _)]
    change (∫ J,B J^(2*q) ∂P) ≤ _
    rw [hh]
    exact hBmom.2
  have hSmom:=hS ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 h2 k1 hh1 hh2 hrs hk
  have hTI:Integrable (fun J=>|T J-s|^(2*q)) P:=hSmom.1
  have hTM:(∫ J,|T J-s|^(2*q) ∂P) ≤ Ks*ε^(2*q):=hSmom.2
  have hWM:Measurable W:=tensor_hessianMatrix_measurable c x e
  have haM:Measurable a:=actual_linearObservation_measurable _
  have huM:Measurable u:=actual_linearObservation_measurable _
  have hDMb:Measurable D:=(fullBorder_measurable hWM k1 haM huM).div_const m
  have hBMb:Measurable B:=((matrixAbsoluteDet_measurable n k1).comp hWM).div_const m
  have hκ:0<κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hTMb:Measurable T:=actualClippedSchurFactor_measurable c x e v k1 hκ
  have hSym (J:Disorder (n+3) μ.maxDegree):(W J).IsHermitian:=by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial,W,hessianMatrix] using hessianEntry_symm c x e j i J
  let G:=W ⁻¹' gapEvent n k1 κ
  have hG:MeasurableSet G:=(gapEvent_measurable n k1 κ).preimage hWM
  have hgood:∀ᵐ J ∂P,J∈G → |D J-|s| * B J| ≤ |B J| * |T J-s|:=by
    filter_upwards [] with J
    intro hJ
    have hp:=border_abs_error_of_norm_gap (W J) (hSym J) k1 hκ hJ (k1-a J) s (u J)
    have hleft:|D J-|s| * B J|=|fullBorder W k1 a u J-|s| * matrixAbsoluteDet n k1 (W J)|/m:=by
      dsimp only [D,B]
      rw [←mul_div_assoc,←sub_div,abs_div,abs_of_pos hm]
    rw [hleft,abs_of_nonneg (hB0 J)]
    exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by
      dsimp only [B,T,actualClippedSchurFactor,m,matrixAbsoluteDet,W,a,u]
      ring)
  have hProb:P.real Gᶜ=(goeLaw (n+1) (n+3) b).real (gapEvent n k1 κ)ᶜ:=by
    rw [←hLaw.map_eq]
    simp only [Measure.real]
    rw [Measure.map_apply hWM (gapEvent_measurable n k1 κ).compl]
    rfl
  have hGap:P.real Gᶜ ≤ Real.exp (-(n+1:ℝ)*(gap/Real.sqrt b)^2/(16*Real.pi^2)):=by
    rw [hProb]
    exact hGapAll (n+3) (by omega) k1 hk
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hInv:1/Real.sqrt (n+3:ℕ) ≤ ε:=le_add_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
  have hRate:=q_error_good_event_rate P D B T hDMb hBMb hTMb s q hq0 hDI hBI hTI G hG hgood n
    (div_pos hgap (Real.sqrt_pos.mpr hb)) hε hInv hKD hKB hKs.le hDM hBM hTM hGap
  have hs:0<s:=physicalSchurMultiplier_pos hb (by linarith)
  have hsM:s ≤ M:=(physicalSchurMultiplier_bounds hb (by linarith)).2.trans hkM
  simp only [abs_of_pos hs] at hRate
  refine ⟨hRate.1,hRate.2.trans ?_⟩
  have hsQ:s^q ≤ M^q:=Real.rpow_le_rpow hs.le hsM hq0
  have hGapC:0 ≤ gapMomentConstant (gap/Real.sqrt b) q:=by unfold gapMomentConstant;positivity
  calc
    _ ≤ K*ε^q:=by dsimp only [K];gcongr
    _ ≤ (1+K)*ε^q:=mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hε q)

end
end SlowEquilibration.SphericalCommonHessianRegression
