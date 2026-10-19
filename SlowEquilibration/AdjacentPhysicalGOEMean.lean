-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SinglePointFullBorderMeanRate
public import SlowEquilibration.SphericalGeometricBorderMeanLaw
public import SlowEquilibration.SphericalPairOrthogonalPoints
public import SlowEquilibration.NormalizedObservationCoercivity

/-! The actual adjacent physical GOE mean comparison at the manuscript's
N^-1/2 rate. Geometry, observer coercivity, Gaussian laws, Schur noise,
ordinary moments and rare-gap terms are all discharged in the model. -/
@[expose] public section
namespace SlowEquilibration.GOEPhysicalPotential
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open SphericalPairCommonFrame SphericalCommonHessianRegression NormalizedPairObservations
open GaussianObservationCoercivity NormalizedObservationCoercivity GOEClippedResolvent GOEScaling
open PhysicalCommonBorderMoments GOERawMoments
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- Source adjacent one-point normalization: every finite mixture of
minimum degree at least three, including pure and odd models, has the
literal adjacent GOE mean ratio 1+O(N^-1/2) uniformly on the exterior compact
window. No observation, frame, determinant comparison, or rate is assumed. -/
theorem source_adjacent_physicalMean_ratio_rate (μ : FiniteMixture) {Q g Z : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) (hg : 0 < g) :
    ∃ C:ℝ,0 < C ∧ ∀ᶠ n:ℕ in atTop,∀ k:ℝ,
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k → k ≤ Z →
      |physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k/
        (physicalSchurMultiplier (Q^2*μ.xi2 Q) k*physicalMean n (n+3) (Q^2*μ.xi2 Q) k)-1| ≤
          C/Real.sqrt (n+3:ℕ) := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=Q^2*μ.xi2 Q
  have hb : 0 < b:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hc : ∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hB : secondCovariance c 1=b := by rw [secondCovariance_center,secondCovariance_mixture]
  have hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val := by
    intro p hp
    have hcoeff : μ.coeff p.val.val≠0 := by
      intro hzero
      apply hp
      simp only [c,centerCoefficients,mixtureCoefficients,hzero,zero_mul]
    exact hd.trans (μ.degree_bounds (Finsupp.mem_support_iff.mpr hcoeff)).1
  let ρ:=g/(4*Real.sqrt b)
  have hρ : 0 < ρ:=by dsimp only [ρ];positivity
  have hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1)) := by
    rw [hB]
    dsimp only [ρ]
    have hs : 0 < Real.sqrt b:=Real.sqrt_pos.mpr hb
    apply div_le_div_of_nonneg_left hg.le (by positivity)
    linarith
  obtain ⟨C,hC,hAll⟩:=actual_single_full_border_value_L1_rate (Z:=Z) c hc (hB.symm ▸ hb) hdeg hg hρ hρg
  obtain ⟨δ,hδ,hCoercive⟩:=uniform_value_coercivity μ hQ
  refine ⟨C/Real.sqrt b,by positivity,?_⟩
  filter_upwards [hAll] with n hn
  intro k hk hkZ
  obtain ⟨x,y,hx,hy,hr⟩:=exists_orthogonal_sphere_pair n
  let e : Fin (n+1) → Vector (n+3):=commonFrame (by omega) x y hx hy hr
  let v:=planeDirection x y
  let f : Fin 0 → Vector (n+3):=Fin.elim0
  have hN : 0 < n+3:=by omega
  have he : Orthonormal ℝ e:=commonFrame_orthonormal hN x y hx hy hr
  have htan : ∀ i,inner ℝ (e i) x=0:=commonFrame_tangent_left hN x y hx hy hr
  have hve : ∀ i,inner ℝ (e i) v=0 := by
    intro i
    exact planeDirection_common_inner x y (e i) (commonFrame_tangent_left hN x y hx hy hr i)
      (commonFrame_tangent_right hN x y hx hy hr i)
  have hv : ‖v‖=1:=planeDirection_norm hN x y hx hy hr
  have hvtan : inner ℝ v x=0:=planeDirection_tangent hN x y hx
  have hf : Orthonormal ℝ f:=by rw [orthonormal_iff_ite];intro i;exact i.elim0
  have hfTan : ∀ i,inner ℝ (f i) x=0:=fun i=>i.elim0
  have hA : Surjective (singleValueObservation c x f):=
    observation_surjective _ hδ (hCoercive (n+3) 0 hN x hx f hf hfTan)
  have hk' : 2*Real.sqrt (secondCovariance c 1)+g ≤ k := by rwa [hB]
  have hh:=hn 0 x v hx hv hvtan e he htan hve f hA (0:ValueObservationSpace 0) k hk' hkZ
  let s:=physicalSchurMultiplier b k
  let m:=physicalMean n (n+3) b k
  have hAdj : (∫ J,fullBorder (hessianMatrix c x e) k
      (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J
      ∂coefficientKernel (singleValueObservation c x f) 0)=physicalMean (n+1) (n+3) (secondCovariance c 1) k := by
    simpa only [e,v] using geometric_fullBorder_value_integral_eq_adjacentMean (n:=n) c hc hdeg x y hx hy hr f 0 k
  have hMean : |physicalMean (n+1) (n+3) b k/m-s| ≤ C/Real.sqrt (n+3:ℕ) := by
    have hm:=hh.2.2
    dsimp only at hm
    rw [integral_div,hAdj,hB] at hm
    exact hm
  have hSpos : 0 < s:=physicalSchurMultiplier_pos hb (by linarith)
  have hSlow : Real.sqrt b ≤ s := by
    have hs:=(physicalSchurMultiplier_bounds (b:=b) (k:=k) hb (by linarith)).1
    linarith
  have hRatioEq : physicalMean (n+1) (n+3) b k/(s*m)-1=
      (physicalMean (n+1) (n+3) b k/m-s)/s := by
    field_simp
  change |physicalMean (n+1) (n+3) b k/(s*m)-1| ≤ _
  rw [hRatioEq,abs_div,abs_of_pos hSpos]
  calc
    _ ≤ (C/Real.sqrt (n+3:ℕ))/s:=div_le_div_of_nonneg_right hMean hSpos.le
    _ ≤ (C/Real.sqrt (n+3:ℕ))/Real.sqrt b :=
      div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hb) hSlow
    _=_:=by ring

/-- The literal adjacent physical GOE mean eventually dominates its
bulk mean by a uniform positive amount on the actual exterior window. -/
theorem source_adjacent_physicalMean_lower_eventually (μ : FiniteMixture) {Q g Z : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) (hg : 0 < g) :
    ∀ᶠ n:ℕ in atTop,∀ k:ℝ,2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k → k ≤ Z →
      0 < physicalMean n (n+3) (Q^2*μ.xi2 Q) k ∧
      0 < physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k ∧
      physicalMean n (n+3) (Q^2*μ.xi2 Q) k/physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k ≤
        2/Real.sqrt (Q^2*μ.xi2 Q) := by
  let b:=Q^2*μ.xi2 Q
  have hb : 0 < b:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨C,hC,hRatio⟩:=source_adjacent_physicalMean_ratio_rate (Z:=Z) μ hQ hd hg
  have hRaw:=GOESharpMoments.goe_determinant_moments_eventually hb hg
  have hRawNext:=((tendsto_add_atTop_nat 1).eventually hRaw)
  filter_upwards [hRatio,hRaw,hRawNext,eventually_ge_atTop (Nat.ceil (4*C^2))] with n hn hR hRN hSize
  intro k hk hkZ
  have hm : 0 < physicalMean n (n+3) b k:=(hR (n+3) (by omega) k hk).2.1
  have hf : 0 < physicalMean (n+1) (n+3) b k:=(hRN (n+3) (by omega) k hk).2.1
  let s:=physicalSchurMultiplier b k
  have hs : 0 < s:=physicalSchurMultiplier_pos hb (by linarith)
  have hsLo : Real.sqrt b ≤ s := by
    have hh:=(physicalSchurMultiplier_bounds (b:=b) (k:=k) hb (by linarith)).1
    linarith
  have hSizeR : 4*C^2 ≤ (n+3:ℕ) := by
    have hh:= (Nat.le_ceil (4*C^2)).trans (show (Nat.ceil (4*C^2):ℝ)≤(n:ℝ) by exact_mod_cast hSize)
    exact hh.trans (by norm_cast;omega)
  have hRoot : 2*C ≤ Real.sqrt (n+3:ℕ) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith)
  have hHalf : C/Real.sqrt (n+3:ℕ) ≤ (1/2:ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hBound:= (hn k hk hkZ).trans hHalf
  have hRatioLo : (1/2:ℝ) ≤ physicalMean (n+1) (n+3) b k/(s*physicalMean n (n+3) b k) := by
    have hh:=(neg_le_neg hBound).trans
      (neg_abs_le (physicalMean (n+1) (n+3) b k/(s*physicalMean n (n+3) b k)-1))
    linarith
  have hMultiply := (le_div_iff₀ (mul_pos hs hm)).mp hRatioLo
  refine ⟨hm,hf,?_⟩
  apply (div_le_div_iff₀ hf (Real.sqrt_pos.mpr hb)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsLo hm.le]

end
end SlowEquilibration.GOEPhysicalPotential
