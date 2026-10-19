-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedDeterminantSelectionLoss
public import SlowEquilibration.SourcePhysicalPairRetainedWindowLimits
public import SlowEquilibration.SourcePureRetainedTailSqueeze
public import SlowEquilibration.MixedAllHighComplete

/-! Posterior selection and determinant loss for manuscript Section 10.
Regularity is discharged internally, the collar is the exact closed π/4
collar, and constants and mark boxes precede dimensions and fixed windows. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedFilterInterface
open MeasureTheory ProbabilityTheory Set Filter Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian SphericalMarkedWindows
open PairConditionalDeterminantMoments ConditionedDeterminantMoments GOEMaximumDeterminant
open SphericalTAPCertificate TwoAtomStationarity LatitudeGroundTrial
open scoped ENNReal Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private theorem scalar_derivative_upper_bound
    (f f' : ℝ → ℝ) (b M : ℝ) (hb : 0 ≤ b)
    (hderiv : ∀ r ∈ Set.Icc (0 : ℝ) b, HasDerivAt f (f' r) r)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) b, f' r ≤ M) :
    f b - f 0 ≤ M*b := by
  rcases hb.eq_or_lt with rfl | hbpos
  · simp
  have hc : ContinuousOn f (Set.Icc (0 : ℝ) b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  obtain ⟨r,hr,hslope⟩ := exists_hasDerivAt_eq_slope f f' hbpos hc
    (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx))
  have hrI : r ∈ Set.Icc (0 : ℝ) b := Set.Ioo_subset_Icc_self hr
  have hle : (f b - f 0)/b ≤ M := by
    have heq : f' r = (f b - f 0)/b := by simpa using hslope
    rw [← heq]
    exact hbound r hrI
  exact (div_le_iff₀ hbpos).mp hle


/-- The closed angle endpoint in `lem:mo-geodesic` still leaves half of
the strictly negative initial curvature. -/
private theorem scalar_collar_closed
    (N C κ θ : ℝ) (hN : 0 < N) (hC : 0 < C) (hκ : 0 < κ)
    (hθ : 0 < θ) (hθsmall : θ ≤ κ/(2*C))
    (s h t : ℝ → ℝ) (hs0 : s 0 = 0) (hh0 : h 0 ≤ -κ*N)
    (hs : ∀ r ∈ Icc (0 : ℝ) θ, HasDerivAt s (h r) r)
    (hh : ∀ r ∈ Icc (0 : ℝ) θ, HasDerivAt h (t r) r)
    (ht : ∀ r ∈ Icc (0 : ℝ) θ, |t r| ≤ C*N) :
    s θ < 0 := by
  have hCN : 0 ≤ C*N := mul_nonneg hC.le hN.le
  have hct : C*θ ≤ κ/2 := by
    calc
      _ ≤ C*(κ/(2*C)) := mul_le_mul_of_nonneg_left hθsmall hC.le
      _ = κ/2 := by field_simp
  have hctN : (C*N)*θ ≤ (κ*N)/2 := by
    nlinarith [mul_le_mul_of_nonneg_right hct hN.le]
  have hneg : ∀ r ∈ Icc (0 : ℝ) θ, h r < 0 := by
    intro r hr
    have hdiff := scalar_derivative_upper_bound h t r (C*N) hr.1
      (fun z hz => hh z (Icc_subset_Icc_right hr.2 hz))
      (fun z hz => (le_abs_self _).trans (ht z (Icc_subset_Icc_right hr.2 hz)))
    have hmul := mul_le_mul_of_nonneg_left hr.2 hCN
    nlinarith [mul_pos hκ hN]
  have hcont : ContinuousOn s (Icc (0 : ℝ) θ) := by
    intro r hr
    exact (hs r hr).continuousAt.continuousWithinAt
  obtain ⟨r, hr, hslope⟩ := exists_hasDerivAt_eq_slope s h hθ hcont
    (fun r hr => hs r (Ioo_subset_Icc_self hr))
  have hdiv : (s θ-s 0)/θ < 0 := by
    have heq : h r = (s θ-s 0)/θ := by simpa only [sub_zero] using hslope
    rw [← heq]
    exact hneg r (Ioo_subset_Icc_self hr)
  have hmul := (div_lt_iff₀ hθ).mp hdiv
  simpa only [hs0, sub_zero, zero_mul] using hmul

/-- The exact manuscript collar `1 - cos (min (π/4) (κ/(2C)))`, including
its boundary. The existing actual-sphere collar first rules out overlap one. -/
private theorem exact_critical_collar {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) (u w : Vector (n+1))
    (hu : ‖u‖^2 = (n+1 : ℕ)) (hw : ‖w‖^2 = (n+1 : ℕ)) (huw : u ≠ w)
    (huc : surfaceGradient (field c J) u = 0)
    (hwc : surfaceGradient (field c J) w = 0)
    (hMargin : sourceHessianMargin c κ J u) (hReg : sourceSphereRegularity c J ≤ C) :
    overlap u w < 1 - (1 - Real.cos (min (Real.pi/4) (κ/(2*C)))) := by
  have hShort := source_actual_sphere_critical_collar_exclusion c J hκ hC
    u w hu hw huw huc hwc hMargin hReg
  have hLoss := (sourceCriticalCollar_parameters hκ hC).1
  have hrLt : overlap u w < 1 := by linarith
  let θ := min (Real.pi/4) (κ/(2*C))
  have hθ : 0 < θ := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ : θ ≤ Real.pi := (min_le_left _ _).trans (by linarith [Real.pi_pos])
  have hCos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by have := min_le_left (Real.pi/4) (κ/(2*C)); dsimp [θ]; linarith [Real.pi_pos]⟩
  by_contra hbad
  have hrLower : Real.cos θ ≤ overlap u w := by
    change ¬ overlap u w < 1 - (1 - Real.cos θ) at hbad
    linarith
  have hrPos : 0 < overlap u w := hCos.trans_le hrLower
  have hAngle : Real.arccos (overlap u w) ≤ θ := by
    have H := Real.arccos_le_arccos hrLower
    rwa [Real.arccos_cos hθ.le hθπ] at H
  obtain ⟨v, hv, huv, hEnd⟩ := sourceSphereGeodesic_reconstruction u w hu hw ⟨hrPos, hrLt⟩
  have hs0 : sourceSphereGeodesicSlope c J u v 0 = 0 := by
    unfold sourceSphereGeodesicSlope
    rw [sourceSphereGeodesicVelocity_zero, sourceSphereGeodesic_zero, huc, inner_zero_right]
  have hh0 : sourceSphereGeodesicCurvature c J u v 0 ≤ -κ*(n+1 : ℕ) := by
    unfold sourceSphereGeodesicCurvature
    rw [sourceSphereGeodesicVelocity_zero, sourceSphereGeodesic_zero]
    have H := hMargin v
    rwa [source_tangentProjection_fixed u v huv, hv] at H
  have H := scalar_collar_closed (n+1 : ℕ) C κ (Real.arccos (overlap u w))
    (by positivity) hC hκ (Real.arccos_pos.mpr hrLt)
    (hAngle.trans (min_le_right _ _))
    (sourceSphereGeodesicSlope c J u v) (sourceSphereGeodesicCurvature c J u v)
    (sourceSphereGeodesicCubic c J u v) hs0 hh0
    (fun t _ => sourceSphereGeodesicSlope_hasDerivAt (by omega) c J u v hu hv huv t)
    (fun t _ => sourceSphereGeodesicCurvature_hasDerivAt (by omega) c J u v hu hv huv t)
    (fun t _ => sourceSphereGeodesicCubic_abs_le (by omega) c J u v hu hv huv hReg t)
  have hsEnd : sourceSphereGeodesicSlope c J u v (Real.arccos (overlap u w)) = 0 := by
    unfold sourceSphereGeodesicSlope
    rw [hEnd, hwc, inner_zero_right]
  rw [hsEnd] at H
  exact (lt_irrefl (0 : ℝ)) H


private theorem failure_rate_exponential (μ : FiniteMixture) {Q G g : ℝ}
    (hQ : 0 < Q) (hG : 0 < G) (hg : 0 < g) (grid : ℕ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ n : ℕ,
      sourceSelectionFailureRate μ Q G g grid n ≤ A*Real.exp (-c*(n+2:ℕ)) := by
  let a := ((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2)
  let b := (G/8)^2/(2*μ.xi Q)
  have hbQ : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; have hξ := μ.xi_pos hQ; positivity
  let c := min (1/2) (min (a/2) b)
  let A := 2*(Fintype.card (Degree μ.maxDegree):ℝ)+1+(grid+1:ℕ)
  refine ⟨c,A,lt_min (by norm_num) (lt_min (by positivity) hb),by dsimp [A]; positivity,?_⟩
  intro n
  have hc1 : c ≤ 1/2 := min_le_left _ _
  have hca : c ≤ a/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have h1 : Real.exp (-(n+2:ℕ)/2) ≤ Real.exp (-c*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc1 (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
  have h2 : Real.exp (-(n+1:ℝ)*a) ≤ Real.exp (-c*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_right hca (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
  have h3 : Real.exp (-(n+2:ℕ)*b) ≤ Real.exp (-c*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
  unfold sourceSelectionFailureRate
  rw [show -(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2) =
    -(n+1:ℝ)*a by dsimp [a]; ring,
    show -(n+2:ℕ)*(G/8)^2/(2*μ.xi Q) = -(n+2:ℕ)*b by dsimp [b]; ring]
  calc
    _ ≤ 2*(Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-c*(n+2:ℕ))+
        Real.exp (-c*(n+2:ℕ))+(grid+1:ℕ)*Real.exp (-c*(n+2:ℕ)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) h2)
        (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = _ := by ring

/-- Deterministic clauses (iii) and (iv) of `thm:mo-filter`, with precisely
the closed π/4 collar and no critical point left at its boundary. -/
theorem selection_exact_exclusion {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+1) P) {κ C ε η E G δ : ℝ}
    (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ 1-Real.cos (min (Real.pi/4) (κ/(2*C)))) (hδ : δ < G/2)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1:ℕ))
    (huc : surfaceGradient (field c J) u = 0)
    (hSel : sourceSelectionEvent c κ C ε η E G J u) :
    (∀ v : Vector (n+1), ‖v‖^2 = (n+1:ℕ) → surfaceGradient (field c J) v = 0 →
      Real.cos (min (Real.pi/4) (κ/(2*C))) ≤ overlap u v → v = u) ∧
    (∀ v : Vector (n+1), ‖v‖^2 = (n+1:ℕ) → surfaceGradient (field c J) v = 0 →
      (n+1:ℕ)*(E-δ) ≤ field c J v → v ≠ u → overlap u v < ε) := by
  have hcollar (v : Vector (n+1)) (hv : ‖v‖^2=(n+1:ℕ))
      (hvc : surfaceGradient (field c J) v=0) (hne : v≠u) :
      overlap u v < Real.cos (min (Real.pi/4) (κ/(2*C))) := by
    have H := exact_critical_collar c J hκ hC u v hu hv hne.symm huc hvc hSel.1 hSel.2.1
    linarith
  constructor
  · intro v hv hvc hOverlap
    by_contra hne
    exact not_lt_of_ge hOverlap (hcollar v hv hvc hne)
  · intro v hv hvc hHigh hne
    have hr : overlap u v ≤ 1-η := by linarith [hcollar v hv hvc hne]
    by_contra hbad
    have H := hSel.2.2 v hv (le_of_not_gt hbad) hr
    have hN : (0:ℝ) < (n+1:ℕ) := by positivity
    nlinarith [mul_pos hN (sub_pos.mpr hδ)]

/-- Posterior clauses of `thm:mo-filter` and `prop:mo-filter-loss(a)` on
one event and one mark box. The full sphere regularity constant precedes ε;
no regularity or first-moment estimate is supplied as a hypothesis. -/
theorem mixed_filter_and_loss (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ C : ℝ, 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) ((g/2)/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ L R δ c A B : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
          2*Real.sqrt (Q^2*μ.xi2 Q)+g < L ∧
          0 < δ ∧ δ < G/4 ∧ δ ≤ 1 ∧ 0 < c ∧ 0 < A ∧ 0 < B ∧
          ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
            ∀ e ∈ Icc (E-δ) (E+δ), ∀ k ∈ Icc L R,
              let cQ := centerCoefficients (mixtureCoefficients μ) Q
              let ν := mixedConditionedLaw cQ u hu (WithLp.toLp 2 ![e,k])
              ν.real {J | ¬sourceSelectionEvent cQ (g/2) C ε η E G J u} ≤
                A*Real.exp (-c*(n+2:ℕ)) ∧
              (∫ J in {J | ¬sourceSelectionEvent cQ (g/2) C ε η E G J u},
                intrinsicDet μ Q u J ∂ν) ≤
                  B*Real.exp (-(c/2)*(n+2:ℕ))*(∫ J, intrinsicDet μ Q u J ∂ν) := by
  dsimp only
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
  let b₀ := markK μ β Q+1
  let M := |E|+1+|a₀|+|b₀|+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  obtain ⟨C,hC,hreg⟩ := source_mixed_physical_posterior_sphere_regularity μ h.overlap_range.1 hnp hM
  let η := 1-Real.cos (min (Real.pi/4) ((g/2)/(2*C)))
  have hθ : 0 < min (Real.pi/4) ((g/2)/(2*C)) := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ : min (Real.pi/4) ((g/2)/(2*C)) < Real.pi/2 :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  have hCos : 0 < Real.cos (min (Real.pi/4) ((g/2)/(2*C))) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθπ⟩
  have hCos1 : Real.cos (min (Real.pi/4) ((g/2)/(2*C))) < 1 := by
    have H := Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=min (Real.pi/4) ((g/2)/(2*C)))
      (by norm_num) (by linarith [Real.pi_pos]) hθ
    simpa only [Real.cos_zero] using H
  have hη : 0 < η := sub_pos.mpr hCos1
  refine ⟨C,hC,hη,by linarith,?_⟩
  intro ε hε hεη
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hG : 0 < G := (source_trial_gap μ h hnp hε hη hεη).1
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδ1,grid,_hgrid,hprob⟩ :=
    source_mixed_physical_posterior_selection_failure_fixed_regularity μ h hnp hε hη hεη
      (by norm_num : (0:ℝ)<1) hC (show |E|+1+|a₀|+|b₀|+1 ≤ M from le_rfl) hreg
  have hgapL : 2*Real.sqrt (Q^2*μ.xi2 Q)+g < L :=
    (hsub (show L ∈ Icc L R from ⟨le_rfl,hL.le.trans hR.le⟩)).1
  obtain ⟨c,A,hc,hA,hrate⟩ := failure_rate_exponential μ h.overlap_range.1 hG hg grid
  obtain ⟨C₂,hC₂,hmom⟩ := mixed_conditioned_determinant_moments μ h.overlap_range.1 hnp
    (g:=g) (Z:=R) (r:=2) hg (by norm_num)
  let B := Real.sqrt C₂*Real.sqrt A
  refine ⟨L,R,δ,c,A,B,hL,hR,hgapL,hδ,hδG,hδ1,hc,hA,by dsimp [B]; positivity,?_⟩
  filter_upwards [hprob] with n hn
  intro u hu e he k hk
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let ν := mixedConditionedLaw cQ u hu (WithLp.toLp 2 ![e,k])
  let : IsProbabilityMeasure ν := by unfold ν mixedConditionedLaw; infer_instance
  have hfail : ν.real {J | ¬sourceSelectionEvent cQ (g/2) C ε η E G J u} ≤
      A*Real.exp (-c*(n+2:ℕ)) := (hn u hu e he k hk).trans (hrate n)
  refine ⟨hfail,?_⟩
  obtain ⟨hD,_hMean,hm,hMom,hMC⟩ := hmom n u hu (WithLp.toLp 2 ![e,k])
    (hgapL.le.trans hk.1) hk.2
  have hBad : MeasurableSet {J : Disorder (n+2) μ.maxDegree |
      ¬sourceSelectionEvent cQ (g/2) C ε η E G J u} :=
    ((sourceSelectionEvent_measurable cQ (g/2) C ε η E G).preimage
      (measurable_id.prodMk measurable_const)).compl
  have H := determinant_event_holder ν (intrinsicDet μ Q u) hD
    (.of_forall (fun _ => abs_nonneg _)) hm _ hBad hMom hMC hfail
  apply (div_le_iff₀ hm).mp
  apply H.trans_eq
  have hs : Real.sqrt (Real.exp (-c*(n+2:ℕ))) = Real.exp (-(c/2)*(n+2:ℕ)) := by
    rw [Real.sqrt_eq_rpow, ←Real.exp_mul]
    congr 1
    ring
  rw [Real.sqrt_mul hA.le,hs]
  dsimp [B]
  ring

/-- Shrinking the mark neighborhood keeps the same event, constants, and
posterior bounds. This is the stability assertion of `thm:mo-filter`. -/
theorem filter_box_shrinking {L R δ L' R' δ' E : ℝ}
    (hL : L ≤ L') (hR : R' ≤ R) (hδ : δ' ≤ δ)
    {e k : ℝ} (he : e ∈ Icc (E-δ') (E+δ')) (hk : k ∈ Icc L' R') :
    e ∈ Icc (E-δ) (E+δ) ∧ k ∈ Icc L R := by
  constructor
  · constructor <;> linarith [he.1,he.2]
  · exact ⟨hL.trans hk.1,hk.2.trans hR⟩


private theorem weighted_count_mono {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {K K' : Set (EuclideanSpace ℝ (Fin 2))} (hKK' : K ⊆ K')
    (ψ ψ' : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (hψ : ∀ J u, ψ J u ≤ ψ' J u) (J : Disorder (n+1) P) :
    actualScoreWindowCount n c K ψ J ≤ actualScoreWindowCount n c K' ψ' J := by
  rw [actualScoreWindowCount_eq_indicator,actualScoreWindowCount_eq_indicator]
  unfold SphericalKacRiceGluing.actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro u
  by_cases hu : actualScore c J u ∈ K
  · simp only [ite_eq_left hu,ite_eq_left (hKK' hu)]
    exact hψ J u
  · simp only [ite_eq_right hu,zero_le]

private theorem retained_mean_mono (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {K K' : Set (EuclideanSpace ℝ (Fin 2))} (hKK' : K ⊆ K')
    (κ C ε η E G : ℝ) :
    sourceRetainedScoreWindowMean (n+1) μ Q K κ C ε η E G ≤
      sourceRetainedScoreWindowMean (n+1) μ Q K' κ C ε η E G := by
  unfold sourceRetainedScoreWindowMean
  have hfinite := bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ K'
    (fun _ _ => 1) 1 (by simp) (by simp)
  have htop := (lintegral_mono (sourceRetainedScoreWindowCount_le_unfiltered (n+1)
    (centerCoefficients (mixtureCoefficients μ) Q) K' κ C ε η E G)).trans_lt hfinite
  apply ENNReal.toReal_mono htop.ne
  exact lintegral_mono (weighted_count_mono (n+1) _ hKK' _ _ (fun _ _ => le_rfl))

private theorem retained_mean_le_maximum_tail (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (H : ℝ) (U : Set ℝ)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : K ⊆ physicalEnergyWindow (n+2) (Ici H) U)
    {κ : ℝ} (hκ : 0 < κ) (C ε η E G : ℝ) :
    sourceRetainedScoreWindowMean (n+1) μ Q K κ C ε η E G ≤
      (sourceMaximumTailCountMass n μ Q H U).toReal := by
  unfold sourceRetainedScoreWindowMean
  rw [sourceMaximumTailCountMass_def]
  have hfinite := sourceMaximumTailCountMass_finite n μ hQ H U
  rw [sourceMaximumTailCountMass_def] at hfinite
  apply ENNReal.toReal_mono hfinite.ne
  apply lintegral_mono_ae
  filter_upwards [actualLocalMaxCount_eq_negative_ae (n+1) (by omega) μ hQ
    (physicalEnergyWindow (n+2) (Ici H) U)] with J hJ
  rw [hJ,actualNegativeCriticalCount_eq_mark,sourceRetainedScoreWindowCount_eq_selected_maxima (n+1) _ K hκ]
  apply weighted_count_mono (n+1) _ hK
  intro A u
  exact mul_le_of_le_one_right zero_le (sourceSelectionMark_le_one _ κ C ε η E G A u)

/-- Retained upper-tail mean with the manuscript's coarse energy box. -/
def retainedTailMean (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ)
    (m : ℕ → ℝ) (δ κ C ε η E G t : ℝ) : ℝ :=
  sourceRetainedScoreWindowMean (n+1) μ Q
    (physicalEnergyWindow (n+2) (Ici (m n+t)) U ∩
      rectangularScoreWindow (Icc (E-δ) (E+δ)) univ) κ C ε η E G

private theorem tail_from_strict_windows (b t : ℝ) (hb : 0 < b)
    (A B : ℕ → ℝ) (W : ℝ → ℕ → ℝ)
    (hB : Tendsto B atTop (𝓝 (Real.exp (-b*t))))
    (hW : ∀ R : ℝ, t < R → Tendsto (W R) atTop (𝓝 (Real.exp (-b*t)-Real.exp (-b*R))))
    (hbound : ∀ n R, t < R → W R n ≤ A n ∧ A n ≤ B n) :
    Tendsto A atTop (𝓝 (Real.exp (-b*t))) := by
  have hdecay : Tendsto (fun R : ℝ => Real.exp (-b*R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  apply tendsto_order.2
  constructor
  · intro r hr
    obtain ⟨R,hR,hsmall⟩ := ((eventually_gt_atTop t).and
      (hdecay.eventually (gt_mem_nhds (sub_pos.mpr hr)))).exists
    filter_upwards [(hW R hR).eventually
      (eventually_gt_nhds (by linarith : r < Real.exp (-b*t)-Real.exp (-b*R)))] with n hn
    exact hn.trans_le (hbound n R hR).1
  · intro r hr
    filter_upwards [hB.eventually (gt_mem_nhds hr)] with n hn
    exact (hbound n (t+1) (by linarith)).2.trans_lt hn

/-- Fixed retained windows and the retained upper tail in
`prop:mo-filter-loss(b)`, with one actual unit-tail center and radial interval.
The coarse energy clipping is retained, even though the upper tail is unbounded. -/
theorem mixed_retained_windows_and_tail (μ : FiniteMixture) {β x Q ε η δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) (hδMax : 0 < δMax) :
    let E := markE μ β x Q
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R C : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧ sourceRadialEdge μ Q < L ∧ 0 < C ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        (∀ a b : ℝ, a < b → Tendsto (fun n : ℕ => sourceRetainedPhysicalWindowMean n μ Q
          (Ioo L R) (d.center n+a) (d.center n+b) (g/2) C ε η E G)
          atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b)))) ∧
        (∀ δ : ℝ, 0 < δ → ∀ t : ℝ, Tendsto (fun n : ℕ =>
          retainedTailMean n μ Q (Ioo L R) d.center δ (g/2) C ε η E G t)
            atTop (𝓝 (Real.exp (-(β*x)*t)))) := by
  dsimp only
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  obtain ⟨L,R,C,hL,hR,hEdge,hC,d,hwindow⟩ :=
    source_mixed_actual_retained_fixed_window_limits μ h hnp hε hη hεη hδMax
  refine ⟨L,R,C,hL,hR,hEdge,hC,d,hwindow,?_⟩
  intro δ hδ t
  let box := rectangularScoreWindow (Icc (E-δ) (E+δ)) univ
  let A := fun n : ℕ => retainedTailMean n μ Q (Ioo L R) d.center δ (g/2) C ε η E G t
  let B := fun n : ℕ => (sourceMaximumTailCountMass n μ Q (d.center n+t) (Ioo L R)).toReal
  let W := fun b : ℝ => fun n : ℕ => sourceRetainedScoreWindowMean (n+1) μ Q
    (physicalEnergyWindow (n+2) (Icc (d.center n+t) (d.center n+b)) (Ioo L R) ∩ box)
      (g/2) C ε η E G
  have hB : Tendsto B atTop (𝓝 (Real.exp (-(β*x)*t))) :=
    (d.tail_limit t).congr' ((sourceMaximumTailCountMass_toReal_eq μ h hnp hEdge ⟨hL,hR⟩).mono
      (fun n hn => (hn (d.center n+t)).symm))
  have hW : ∀ b : ℝ, t < b → Tendsto (W b) atTop (𝓝 (Real.exp (-(β*x)*t)-Real.exp (-(β*x)*b))) := by
    intro b htb
    apply (hwindow t b htb).congr'
    filter_upwards [source_logarithmic_center_offset_bounds (mul_pos h.beta_pos h.weight_range.1)
      d.log_constant_pos.le hδ d.center d.logarithmic_correction t b] with n hn
    have hsub : physicalEnergyWindow (n+2) (Icc (d.center n+t) (d.center n+b)) (Ioo L R) ⊆ box := by
      intro z hz
      have H := source_physical_window_subset_coarse hn.1 hn.2 hz
      exact ⟨H.1,mem_univ _⟩
    dsimp [W,sourceRetainedPhysicalWindowMean]
    rw [inter_eq_left.mpr hsub]
  apply tail_from_strict_windows (β*x) t (mul_pos h.beta_pos h.weight_range.1) A B W hB hW
  intro n b _htb
  constructor
  · apply retained_mean_mono n μ h.overlap_range.1
    intro z hz
    exact ⟨⟨hz.1.1.1,hz.1.2⟩,hz.2⟩
  · exact retained_mean_le_maximum_tail n μ h.overlap_range.1 (d.center n+t) (Ioo L R)
      inter_subset_left (half_pos hg) C ε η E G

end SlowEquilibration.SourceMixedFilterInterface
