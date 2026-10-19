-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorDeletedGradientBounds
public import SlowEquilibration.SphericalOverlapExponentialGridGeometry

/-! Genuine Brownian short-cell tangent-cutoff bound for the literal deleted
posterior field, on the actual original tensor regularity event. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps SphericalDynamics SphericalMarkedWindows
open SphericalC1Dynamics SphericalOverlapExponential ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
variable {N : ℕ}

def gradientScore (G x : Vector N) : ℝ := inner ℝ G x/(N:ℝ)

def gradientAxis (G : Vector N) : Vector N := (Real.sqrt (N:ℝ)/‖G‖) • G

theorem gradientAxis_onSphere (_hN : 1≤N) (G : Vector N) (hG : G≠0) :
    OnSphere (gradientAxis G) := by
  apply (onSphere_iff_norm_sq _).mpr
  rw [gradientAxis,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hG)]
  exact Real.sq_sqrt (Nat.cast_nonneg N)

theorem gradientScore_eq_scaled_overlap (hN : 1≤N) (G : Vector N) (hG : G≠0) (x : Vector N) :
    gradientScore G x=(‖G‖/Real.sqrt (N:ℝ))*overlapValue (gradientAxis G) x := by
  have hNs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))).ne'
  rw [gradientScore,overlapValue_eq,gradientAxis,real_inner_smul_left]
  field_simp [hNs,norm_ne_zero_iff.mpr hG]

theorem gradientScore_badGrid_probability (hN : 1≤N) {β C K : ℝ}
    (hβ : 0≤β) (hC : 0≤C) (hK : 0<K) (g : Vector N→Vector N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y→‖g y‖≤C*Real.sqrt (N:ℝ))
    (G x : Vector N) (hGnorm : ‖G‖≤K*Real.sqrt (N:ℝ)) (hx : OnSphere x)
    {α : ℝ} (hα : 0<α) (H T : ℝ≥0) (hT : 0<T)
    (hshort : 4*(1+β*C)*(T:ℝ)≤α/(2*K)) :
    (VectorBrownian.law N).real (badGrid (fun t ω=>gradientScore G (process β g hg x t ω)) H T (α/2))≤
      (gridSize H T:ℝ)*2*Real.exp (-(N:ℝ)*(α/(2*K))^2/(16*(T:ℝ))) := by
  by_cases hG : G=0
  · have he : badGrid (fun t ω=>gradientScore G (process β g hg x t ω)) H T (α/2)=∅ := by
      ext ω
      simp only [badGrid,gradientScore,hG,inner_zero_left,zero_div,sub_self,abs_zero,mem_ofPred_eq,mem_empty_iff_false]
      have hh : ¬α/2<0 := not_lt.mpr (by positivity)
      simp only [hh,and_false,exists_false]
    rw [he,measureReal_empty]
    positivity
  · let a := ‖G‖/Real.sqrt (N:ℝ)
    have ha : 0≤a := by unfold a; positivity
    have hNs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have haK : a≤K := (div_le_iff₀ hNs).mpr hGnorm
    have he (y : Vector N) := gradientScore_eq_scaled_overlap hN G hG y
    have hsub : badGrid (fun t ω=>gradientScore G (process β g hg x t ω)) H T (α/2)⊆
        badGrid (fun t ω=>overlapValue (gradientAxis G) (process β g hg x t ω)) H T (α/(2*K)) := by
      rintro ω ⟨j,v,hv,hh⟩
      refine ⟨j,v,hv,?_⟩
      dsimp only at hh ⊢
      rw [he,he,←mul_sub,abs_mul,abs_of_nonneg ha] at hh
      by_contra hn
      have hd : |overlapValue (gradientAxis G) (process β g hg x (gridStart T j.val+v) ω)-
          overlapValue (gradientAxis G) (process β g hg x (gridStart T j.val) ω)|≤α/(2*K) := le_of_not_gt hn
      have hp := mul_le_mul haK hd (abs_nonneg _) hK.le
      have hk : K*(α/(2*K))=α/2 := by field_simp
      rw [hk] at hp
      exact (not_lt_of_ge hp) hh
    exact (measureReal_mono hsub).trans
      (badGrid_probability (by omega) hβ hC g hg hgrad (gradientAxis G) x
        (gradientAxis_onSphere hN G hG) hx (by positivity) H T hT hshort)

theorem mixedProcess_ae_C1Process (hN : 1≤N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t,
      mixedProcess μ J β x t ω=process β (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) x t ω := by
  have hg : ContDiff ℝ 1 (mixedGradient μ J) := (mixedGradient_contDiff μ J).of_le (by simp)
  have hh : ∀ᵐ ω ∂VectorBrownian.law N, ∀ m : ℕ, ∀ t, t≤(m:ℝ≥0)→
      mixedProcess μ J β x t ω=process β (mixedGradient μ J) hg x t ω := by
    apply ae_all_iff.mpr
    intro m
    exact physicalSolution_unique (NullAugmentation.driver (VectorBrownian.driver N)) β
      (mixedGradient μ J) hg x m _ _ (mixedProcess_physical (by omega) μ J β x hx m)
      (process_physical (by omega) β _ hg x hx m)
      ((mixedProcess_onSphere (by omega) μ J β x hx).mono fun ω h t _=>h t)
      ((process_onSphere (by omega) β _ hg x hx).mono fun ω h t _=>h t)
  filter_upwards [hh] with ω hω
  intro t
  obtain ⟨m,hm⟩ := exists_nat_ge t
  exact hω m t hm

theorem actual_mixedPosterior_gradient_shortCells (n : ℕ) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e k : ℝ)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (hz : unpackDisorder z∈regularDisorder)
    {β : ℝ} (hβ : 0≤β) (x : Vector (n+1)) (hx : OnSphere x)
    {α : ℝ} (hα : 0<α) (H T : ℝ≥0) (hT : 0<T)
    (hshort : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ)≤α/(2*centerConstant μ Q)) :
    let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder z)) u
    let J := unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) z)
    (VectorBrownian.law (n+1)).real (badGrid (fun t ω=>gradientScore G (mixedProcess μ J β x t ω)) H T (α/2))≤
      (gridSize H T:ℝ)*2*Real.exp (-((n+1:ℕ):ℝ)*(α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) := by
  dsimp only
  let J := unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) z)
  have he : badGrid (fun t ω=>gradientScore
      (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder z)) u)
        (mixedProcess μ J β x t ω)) H T (α/2)=ᵐ[VectorBrownian.law (n+1)]
      badGrid (fun t ω=>gradientScore
        (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder z)) u)
          (process β (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) x t ω)) H T (α/2) := by
    filter_upwards [mixedProcess_ae_C1Process (by omega) μ J β x hx] with ω hω
    simp only [badGrid,mem_ofPred_eq,hω]
  rw [measureReal_congr he]
  exact gradientScore_badGrid_probability (by omega) hβ (mixedDeletedGradientConstant_nonneg μ Q e k)
    (centerConstant_pos μ Q) _ _ (actual_mixedDeleted_gradient_regular_bound n μ hnp Q hQ hQ1 u hu e k z hz)
    _ x (actual_original_gradient_regular_bound n μ hnp Q hQ hQ1 u hu z hz) hx hα H T hT hshort

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
