-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedOnePointComplete
public import SlowEquilibration.SphericalTAPCriticalLightCountTransfer
public import SlowEquilibration.SourcePureCriticalActualTailBridge

/-! Simultaneous retention and the common one-point interface in manuscript
Section 10. All counts are ordinary counts of points on the physical sphere.
The bad-point count is obtained from the actual posterior determinant loss
and the marked Kac--Rice formula, without an independence assumption. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMixedOnePointInterface
open MeasureTheory ProbabilityTheory Set Filter Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalMarkedWindows SphericalSequentialRegression IntrinsicHessianLaw SphericalPosteriorMaps
open SphericalTAPCertificate TwoAtomStationarity LatitudeGroundTrial
open PairConditionalDeterminantMoments ConditionedDeterminantMoments GOEMaximumDeterminant
open SourceMixedOnePointLiteral SourceMixedFilterInterface SourceMixedOnePointComplete
open SphericalTAPCriticalLightCountTransfer SourcePureDeterminantDerivative
open scoped ENNReal NNReal Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] Classical.propDecidable

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

/-- The actual first moment of critical points failing their selection
event in a specified normalized mark set. -/
def discardedScoreMass (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G : ℝ) : ℝ≥0∞ :=
  ∫⁻ J, actualScoreWindowCount (n+1)
    (centerCoefficients (mixtureCoefficients μ) Q) K
    (sourceDiscardedMark (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G) J
      ∂disorderLaw (n+2) μ.maxDegree

private theorem discarded_le_of_partition {T R B : ℝ≥0∞} {t : ℝ}
    (hT : T < ⊤) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpart : R+B=T) (hlo : ENNReal.ofReal (1-t)*T ≤ R) :
    B ≤ ENNReal.ofReal t*T := by
  have hR : R < ⊤ := (le_add_right le_rfl).trans_lt (hpart.trans_lt hT)
  have hB : B < ⊤ := (le_add_left le_rfl).trans_lt (hpart.trans_lt hT)
  have hp := congrArg ENNReal.toReal hpart
  rw [ENNReal.toReal_add hR.ne hB.ne] at hp
  have hl := ENNReal.toReal_mono hR.ne hlo
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr ht1)] at hl
  apply (ENNReal.toReal_le_toReal hB.ne
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.ne)).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal ht0]
  nlinarith

private theorem mixed_discarded_mass_le (μ : FiniteMixture)
    {β x Q κ C ε η L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hF : MixedFilterOn μ β x Q κ C ε η L R δ) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
        K ⊆ rectangularScoreWindow
          (Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) (Icc L R) →
        discardedScoreMass n μ Q K κ C ε η (markE μ β x Q)
          (gap μ Q (markY β Q) (markZ x Q) ε η) ≤ 
          ENNReal.ofReal (B*Real.exp (-c*(n+2:ℕ))) * sourceMarkedOriginalCountMass n μ Q K := by
  obtain ⟨c,A,B,hc,_hA,hB,hpost⟩ := hF
  have ht : Tendsto (fun n : ℕ => B*Real.exp (-(c/2)*(n+2:ℕ))) atTop (𝓝 0) := by
    have H := (source_dimension_exp_tail_tendsto 2 (half_pos hc)).const_mul B
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  refine ⟨c/2,B,half_pos hc,hB,?_⟩
  filter_upwards [hpost,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn herr
  intro K hK hbox
  have hlo := source_mixed_retained_window_mass_lower (n+1) (by omega) μ
    h.overlap_range.1 hnp K hK κ C ε η (markE μ β x Q)
      (gap μ Q (markY β Q) (markZ x Q) ε η) (B*Real.exp (-(c/2)*(n+2:ℕ))) (by
        intro u hu z hz
        have hmarks := hbox hz
        have hzEq : scorePairEquiv (z 0,z 1)=z := by
          apply PiLp.ext
          intro i
          fin_cases i <;> rfl
        have H := (hn u hu (z 0) hmarks.1 (z 1) hmarks.2).2.2
        rw [hzEq] at H
        exact H)
  have hpart := sourceRetainedScoreWindowMean_add_discarded (n+1) (by omega) μ
    h.overlap_range.1 hnp K hK κ C ε η (markE μ β x Q)
      (gap μ Q (markY β Q) (markZ x Q) ε η)
  rw [sourceMarkedOriginalCountMass_def]
  exact discarded_le_of_partition
    (bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ h.overlap_range.1 K
      (fun _ _ => 1) 1 (by simp) (fun _ _ => le_rfl)) (by positivity) herr.le hpart hlo

/-- Shrinking only the energy width makes the expected number of discarded
high critical points exponentially small. The radial interval and the
selection event are unchanged, as in `prop:mo-filter-loss(d)`. -/
theorem mixed_discarded_high_count_exponential (μ : FiniteMixture)
    {β x Q κ C ε η L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hδ : 0 < δ)
    (hF : MixedFilterOn μ β x Q κ C ε η L R δ) :
    ∃ δ' c : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      discardedScoreMass n μ Q
        (rectangularScoreWindow (Icc (markE μ β x Q-δ') (markE μ β x Q+δ)) (Ioo L R))
        κ C ε η (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η) ≤ 
          ENNReal.ofReal (Real.exp (-c*(n+2:ℕ))) := by
  obtain ⟨c,B,hc,hB,hbad⟩ := mixed_discarded_mass_le μ h hnp hF
  obtain ⟨D,hD,hcoarse⟩ := coarse_count_literal μ h hnp hL (R:=R)
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  let δ' := min δ (c/(2*(β*x)))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hrate : (β*x)*δ' ≤ c/2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2*(β*x))).mp
      (min_le_right δ (c/(2*(β*x))))
    dsimp [δ']
    nlinarith
  have hDim : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  refine ⟨δ',c/4,hδ',min_le_left _ _,by positivity,?_⟩
  filter_upwards [hbad,hDim.eventually_ge_atTop
    (StrongFieldComplexity.polynomialAbsorptionThreshold (B*D) 1 (c/4))] with n hn hN
  let K := rectangularScoreWindow (Icc (markE μ β x Q-δ') (markE μ β x Q+δ)) (Ioo L R)
  have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Ioo
  have hbox : K ⊆ rectangularScoreWindow
      (Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) (Icc L R) := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1,min_le_left δ (c/(2*(β*x)))],hz.1.2⟩,
      Ioo_subset_Icc_self hz.2⟩
  have hmass : sourceMarkedOriginalCountMass n μ Q K ≤ 
      sourceMarkedOriginalCountMass n μ Q
        (rectangularScoreWindow (Ici (markE μ β x Q-δ')) (Ioo L R)) := by
    rw [sourceMarkedOriginalCountMass_def,sourceMarkedOriginalCountMass_def]
    exact lintegral_mono (weighted_count_mono (n+1) _
      (show K ⊆ rectangularScoreWindow (Ici (markE μ β x Q-δ')) (Ioo L R) from fun _ hz => ⟨hz.1.1,hz.2⟩) _ _ (fun _ _ => le_rfl))
  have hpoly := StrongFieldComplexity.polynomial_le_exp_of_threshold (B:=B*D) 1
    (by positivity) (show 0 < c/4 by positivity) hN
  simp only [pow_one] at hpoly
  calc
    _ ≤ ENNReal.ofReal (B*Real.exp (-c*(n+2:ℕ))) * sourceMarkedOriginalCountMass n μ Q K := hn K hK hbox
    _ ≤ ENNReal.ofReal (B*Real.exp (-c*(n+2:ℕ))) *
        ENNReal.ofReal (D*(n+2:ℕ)*Real.exp ((β*x)*δ'*(n+2:ℕ))) :=
      mul_le_mul' le_rfl (hmass.trans (hcoarse n δ' hδ'.le))
    _ = ENNReal.ofReal ((B*D*(n+2:ℕ))*Real.exp ((-c+(β*x)*δ')*(n+2:ℕ))) := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (-c+(β*x)*δ')*(n+2:ℕ) = -c*(n+2:ℕ)+(β*x)*δ'*(n+2:ℕ) by ring,
        Real.exp_add]
      ring
    _ ≤ ENNReal.ofReal (Real.exp (c/4*(n+2:ℕ))*Real.exp (-(c/2)*(n+2:ℕ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul hpoly _ (by positivity) (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hrate (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

/-- The actual all-critical upper-tail count in raw energy, with the
same radial interval as the maximum intensity. -/
def mixedCriticalTailMass (n : ℕ) (μ : FiniteMixture) (Q H : ℝ) (U : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ J, actualScoreWindowCount (n+1)
    (centerCoefficients (mixtureCoefficients μ) Q)
    (physicalEnergyWindow (n+2) (Ici H) U) (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree

def mixedCriticalTailMean (n : ℕ) (μ : FiniteMixture) (Q H : ℝ) (U : Set ℝ) : ℝ :=
  (mixedCriticalTailMass n μ Q H U).toReal

private theorem mixedCriticalTailMass_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (H : ℝ) (U : Set ℝ) :
    mixedCriticalTailMass n μ Q H U < ⊤ := by
  unfold mixedCriticalTailMass
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ _
    (fun _ _ => 1) 1 (by simp) (fun _ _ => le_rfl)

private theorem mixed_tail_relative_comparison (μ : FiniteMixture) {Q L R : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ => maximumRelativeError C (Q^2*μ.xi2 Q)
        ((L-sourceRadialEdge μ Q)/2) n) atTop (𝓝 (0 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop,
        0 ≤ maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n ∧
        maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n < 1 ∧
        ∀ H : ℝ,
          (1-maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n)*
            mixedCriticalTailMean n μ Q H (Ioo L R) ≤ 
              (sourceMaximumTailCountMass n μ Q H (Ioo L R)).toReal ∧
          (sourceMaximumTailCountMass n μ Q H (Ioo L R)).toReal ≤ 
            mixedCriticalTailMean n μ Q H (Ioo L R) := by
  let g := (L-sourceRadialEdge μ Q)/2
  have hg : 0 < g := half_pos (sub_pos.mpr hL)
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨C,hC,hbound⟩ := mixed_physical_maximum_relative_comparison μ hQ (Z := R) hg
  refine ⟨C,hC,maximumRelativeError_tendsto_zero hb hg C,?_⟩
  filter_upwards [hbound] with n hn
  refine ⟨hn.1,hn.2.1,?_⟩
  intro H
  have hMax : sourceMaximumTailCountMass n μ Q H (Ioo L R)=
      ∫⁻ v in Ici H, ∫⁻ k in Ioo L R, mixedLocalMaxPhysicalIntensity n μ Q v k := by
    rw [sourceMaximumTailCountMass_def]
    exact actual_mixed_localMax_physical_intensity n μ hQ hnp _ _ measurableSet_Ici measurableSet_Ioo
  have hAll : mixedCriticalTailMass n μ Q H (Ioo L R)=
      ∫⁻ v in Ici H, ∫⁻ k in Ioo L R, mixedCriticalPhysicalIntensity n μ Q v k := by
    unfold mixedCriticalTailMass
    exact actual_mixed_critical_physical_intensity n μ hQ hnp _ _ measurableSet_Ici measurableSet_Ioo
  have hMarks : ∀ k ∈ Ioo L R, k ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) R := by
    intro k hk
    dsimp [g,sourceRadialEdge] at *
    constructor <;> linarith [hk.1,hk.2]
  have hlo : ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
      mixedCriticalTailMass n μ Q H (Ioo L R) ≤ sourceMaximumTailCountMass n μ Q H (Ioo L R) := by
    rw [hMax,hAll]
    calc
      _ = (∫⁻ v in Ici H, ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
          (∫⁻ k in Ioo L R, mixedCriticalPhysicalIntensity n μ Q v k)) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = (∫⁻ v in Ici H, ∫⁻ k in Ioo L R,
          ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*mixedCriticalPhysicalIntensity n μ Q v k) := by
        apply lintegral_congr
        intro v
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro v
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
        exact (hn.2.2 v k (hMarks k hk)).1
  have hup : sourceMaximumTailCountMass n μ Q H (Ioo L R) ≤ mixedCriticalTailMass n μ Q H (Ioo L R) := by
    rw [hMax,hAll]
    apply lintegral_mono
    intro v
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
    exact (hn.2.2 v k (hMarks k hk)).2
  have hloReal := ENNReal.toReal_mono (sourceMaximumTailCountMass_finite n μ hQ H (Ioo L R)).ne hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hn.2.1.le)] at hloReal
  have hupReal := ENNReal.toReal_mono (mixedCriticalTailMass_finite n μ hQ H (Ioo L R)).ne hup
  exact ⟨hloReal,hupReal⟩

/-- The all-critical upper-tail limit at the same exact unit-maximum-tail
center. This supplies the previously missing unbounded tail in
`cor:mo-interface(ii)`. -/
theorem mixed_all_critical_tail_limit (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) (t : ℝ) :
    Tendsto (fun n : ℕ => mixedCriticalTailMean n μ Q (d.center n+t) (Ioo L R))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  obtain ⟨C,_hC,herror,hbound⟩ := mixed_tail_relative_comparison μ h.overlap_range.1 hnp hL (R := R)
  have hmax : Tendsto (fun n : ℕ => (sourceMaximumTailCountMass n μ Q (d.center n+t) (Ioo L R)).toReal)
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    apply (d.tail_limit t).congr'
    filter_upwards [sourceMaximumTailCountMass_toReal_eq μ h hnp hL hm] with n hn
    exact (hn (d.center n+t)).symm
  have hupper : Tendsto (fun n : ℕ =>
      (sourceMaximumTailCountMass n μ Q (d.center n+t) (Ioo L R)).toReal/
        (1-maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    simpa only [sub_zero,div_one,Pi.div_def,Pi.sub_def] using
      hmax.div (tendsto_const_nhds.sub herror) (by norm_num : (1 : ℝ)-0 ≠ 0)
  apply hmax.squeeze' hupper
  · filter_upwards [hbound] with n hn
    exact (hn.2.2 (d.center n+t)).2
  · filter_upwards [hbound] with n hn
    apply (le_div_iff₀ (sub_pos.mpr hn.2.1)).mpr
    exact (mul_comm _ _).trans_le (hn.2.2 (d.center n+t)).1

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


private theorem count_event_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f : Ω → ℝ≥0∞) (hf : AEMeasurable f ν)
    {b : ℝ} (hb : 0 ≤ b) (hmean : (∫⁻ w, f w ∂ν) ≤ ENNReal.ofReal b) :
    ν.real (toMeasurable ν {w | 1 ≤ f w}) ≤ b := by
  have H : ν (toMeasurable ν {w | 1 ≤ f w}) ≤ ENNReal.ofReal b := by
    rw [measure_toMeasurable]
    have hm : ν {w | 1 ≤ f w} ≤ ∫⁻ w, f w ∂ν := by
      simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hf 1
    exact hm.trans hmean
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top H).trans_eq (ENNReal.toReal_ofReal hb)

private theorem event_probability_all_dimensions (μ : FiniteMixture)
    (Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree)) {c A : ℝ} (hc : 0 < c)
    (hprob : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ A*Real.exp (-c*(n+2:ℕ))) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ B*Real.exp (-c*(n+2:ℕ)) := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hprob
  let B := max A (Real.exp (c*(n₀+2:ℕ)))+1
  have hB : 0 < B := by
    have := le_max_right A (Real.exp (c*(n₀+2:ℕ)))
    dsimp [B]
    linarith [Real.exp_pos (c*(n₀+2:ℕ))]
  refine ⟨B,hB,?_⟩
  intro n
  by_cases hn : n₀ ≤ n
  · exact (hn₀ n hn).trans (mul_le_mul_of_nonneg_right
      (by have := le_max_left A (Real.exp (c*(n₀+2:ℕ))); dsimp [B]; linarith)
      (Real.exp_pos _).le)
  · apply measureReal_le_one.trans
    have hnn : (n+2:ℝ) ≤ (n₀+2:ℕ) := by exact_mod_cast (show n+2 ≤ n₀+2 by omega)
    have he : 1 ≤ Real.exp (c*(n₀+2:ℕ))*Real.exp (-c*(n+2:ℕ)) := by
      rw [←Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      push_cast at hnn ⊢
      nlinarith
    exact he.trans (mul_le_mul_of_nonneg_right
      (by have := le_max_right A (Real.exp (c*(n₀+2:ℕ))); dsimp [B]; linarith)
      (Real.exp_pos _).le)

/-- A single Borel event retains every high critical point, including its
coarse mark box, negative Hessian margin and full-sphere regularity. The
selection event is exactly the original one and uses no new energy width. -/
def SimultaneousRetentionOn (μ : FiniteMixture) (β x Q κ C ε η L R δ : ℝ) : Prop :=
  ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
    ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
      (∀ n, MeasurableSet (Ω n)) ∧
      (∀ n, (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ A*Real.exp (-c*(n+2:ℕ))) ∧
      ∀ n J, J ∈ Ω n →
        sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J ≤ C ∧
        (∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
          ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖ ≤ 
            C/Real.sqrt (n+2:ℕ)) ∧
        ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
          surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 →
          (n+2:ℕ)*(markE μ β x Q-δ) ≤ 
            field (centerCoefficients (mixtureCoefficients μ) Q) J u →
          field (centerCoefficients (mixtureCoefficients μ) Q) J u ≤ 
            (n+2:ℕ)*(markE μ β x Q+δ) ∧
          actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R ∧
          sourceSelectionEvent (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η
            (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η) J u

/-- `prop:mo-filter-loss(d)`: only δ is decreased; U, ε and the selection
event remain fixed. Every high critical point is simultaneously selected. -/
theorem mixed_simultaneous_retention (μ : FiniteMixture)
    {β x Q κ C ε η L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hδ : 0 < δ)
    (hHigh : AllHighOn μ β x Q κ C L R δ)
    (hF : MixedFilterOn μ β x Q κ C ε η L R δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      SimultaneousRetentionOn μ β x Q κ C ε η L R δ' := by
  obtain ⟨δ',b,hδ',hδle,hb,hbad⟩ := mixed_discarded_high_count_exponential μ h hnp hL hδ hF
  obtain ⟨e,he,hupper⟩ := sourceAboveContactCountMass_exponential μ h hnp hδ'
  obtain ⟨a,A,ha,hA,Ω₀,hΩ₀m,hΩ₀p,hΩ₀⟩ := hHigh
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let K := rectangularScoreWindow (Icc (E-δ') (E+δ)) (Ioo L R)
  let T := rectangularScoreWindow (Ici (E+δ')) univ
  let B (n : ℕ) := actualScoreWindowCount (n+1) cQ K (sourceDiscardedMark cQ κ C ε η E G)
  let U (n : ℕ) := actualScoreWindowCount (n+1) cQ T (fun _ _ => 1)
  let bad (n : ℕ) := toMeasurable (disorderLaw (n+2) μ.maxDegree) {J | 1 ≤ B n J}
  let upper (n : ℕ) := toMeasurable (disorderLaw (n+2) μ.maxDegree) {J | 1 ≤ U n J}
  let Ω (n : ℕ) := (Ω₀ n ∩ (bad n)ᶜ) ∩ (upper n)ᶜ
  have hΩm (n : ℕ) : MeasurableSet (Ω n) :=
    ((hΩ₀m n).inter (measurableSet_toMeasurable _ _).compl).inter
      (measurableSet_toMeasurable _ _).compl
  have hgood : ∀ n J, J ∈ Ω n →
      sourceSphereRegularity cQ J ≤ C ∧
      (∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
        ‖sourceSphereThirdExtension cQ J u‖ ≤ C/Real.sqrt (n+2:ℕ)) ∧
      ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) → surfaceGradient (field cQ J) u=0 →
        (n+2:ℕ)*(E-δ') ≤ field cQ J u →
        field cQ J u ≤ (n+2:ℕ)*(E+δ') ∧ actualScore cQ J u 1 ∈ Ioo L R ∧
          sourceSelectionEvent cQ κ C ε η E G J u := by
    intro n J hJ
    obtain ⟨⟨hOld,hNotBad⟩,hNotUpper⟩ := hJ
    obtain ⟨hreg,hthird,hcrit⟩ := hΩ₀ n J hOld
    refine ⟨hreg,hthird,?_⟩
    intro u hu huc hhigh
    have hhighOld : (n+2:ℕ)*(E-δ) ≤ field cQ J u :=
      (mul_le_mul_of_nonneg_left (by linarith) (show (0:ℝ) ≤ (n+2:ℕ) by positivity)).trans hhigh
    obtain ⟨hUpOld,hMark,_hMargin⟩ := hcrit u hu huc hhighOld
    have hUp : field cQ J u ≤ (n+2:ℕ)*(E+δ') := by
      by_contra hbadUp
      apply hNotUpper
      apply subset_toMeasurable _ _
      have hwin : actualScore cQ J u ∈ T := by
        refine ⟨?_,mem_univ _⟩
        rw [actualScore_value_eq]
        apply (le_div_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr
        simpa only [mul_comm] using (lt_of_not_ge hbadUp).le
      exact ENNReal.le_tsum (f:=fun _z : {z : Vector (n+2) | ‖z‖^2=(n+2:ℕ) ∧
        surfaceGradient (field cQ J) z=0 ∧ actualScore cQ J z ∈ T} => (1:ℝ≥0∞))
        ⟨u,hu,huc,hwin⟩
    refine ⟨hUp,hMark,?_⟩
    by_contra hNotSel
    apply hNotBad
    apply subset_toMeasurable _ _
    have hwin : actualScore cQ J u ∈ K := by
      refine ⟨⟨?_,?_⟩,hMark⟩
      · rw [actualScore_value_eq]
        exact (le_div_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr (by simpa only [mul_comm] using hhigh)
      · rw [actualScore_value_eq]
        exact (div_le_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr (by simpa only [mul_comm] using hUpOld)
    have H := ENNReal.le_tsum (f:=fun z : {z : Vector (n+2) | ‖z‖^2=(n+2:ℕ) ∧
      surfaceGradient (field cQ J) z=0 ∧ actualScore cQ J z ∈ K} =>
        sourceDiscardedMark cQ κ C ε η E G J z) ⟨u,hu,huc,hwin⟩
    simpa only [sourceDiscardedMark,ite_eq_right hNotSel,B,actualScoreWindowCount,
      mem_ofPred_eq,show n+1+1=n+2 by omega] using H
  let c := min a (min b e)
  have hc : 0 < c := lt_min ha (lt_min hb he)
  have hp : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ (A+2)*Real.exp (-c*(n+2:ℕ)) := by
    filter_upwards [hbad,hupper] with n hn hu
    have hBm : AEMeasurable (B n) (disorderLaw (n+2) μ.maxDegree) :=
      actualScoreWindowCount_aemeasurable (n+1) (by omega) μ h.overlap_range.1 K
        (rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Ioo) _
          (sourceDiscardedMark_measurable cQ κ C ε η E G)
    have hUm : AEMeasurable (U n) (disorderLaw (n+2) μ.maxDegree) :=
      actualScoreWindowCount_aemeasurable (n+1) (by omega) μ h.overlap_range.1 T
        (rectangularScoreWindow_measurable _ _ measurableSet_Ici MeasurableSet.univ) _ measurable_const
    have hB := count_event_probability_le _ _ hBm (Real.exp_pos _).le hn
    have hU := count_event_probability_le _ _ hUm (Real.exp_pos _).le (by
      simpa only [sourceMarkedOriginalCountMass_def] using hu)
    have hUnion : (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ 
        A*Real.exp (-a*(n+2:ℕ))+Real.exp (-b*(n+2:ℕ))+Real.exp (-e*(n+2:ℕ)) := by
      have hsub : (Ω n)ᶜ ⊆ ((Ω₀ n)ᶜ ∪ bad n) ∪ upper n := by
        simp only [Ω,compl_inter,compl_compl]
        exact Subset.rfl
      exact (measureReal_mono hsub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add
          ((measureReal_union_le _ _).trans (add_le_add (hΩ₀p n) hB)) hU))
    have hrate {r : ℝ} (hr : c ≤ r) : Real.exp (-r*(n+2:ℕ)) ≤ Real.exp (-c*(n+2:ℕ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hr (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
    apply hUnion.trans
    calc
      _ ≤ A*Real.exp (-c*(n+2:ℕ))+Real.exp (-c*(n+2:ℕ))+Real.exp (-c*(n+2:ℕ)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hrate (min_le_left _ _)) hA.le) (hrate ((min_le_right _ _).trans (min_le_left _ _))))
          (hrate ((min_le_right _ _).trans (min_le_right _ _)))
      _ = _ := by ring
  obtain ⟨D,hD,hprob⟩ := event_probability_all_dimensions μ Ω hc hp
  exact ⟨δ',hδ',hδle,c,D,hc,hD,Ω,hΩm,hprob,hgood⟩

/-- The completed mixed one-point package, including the all-critical
upper tail on the actual normalized center and simultaneous retention after
shrinking only the coarse energy width. Every probabilistic input is proved. -/
theorem mixed_onePoint_interface (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : sourceRadialEdge μ Q < L₀) (hm : markK μ β Q ∈ Ioo L₀ R₀) :
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧
          δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          Admissible μ β x Q L R δ ∧ AllHighOn μ β x Q κ C L R δ ∧
          MixedFilterOn μ β x Q κ C ε η L R δ ∧
          MixedRetainedRatioOn μ β x Q κ C ε η L R δ ∧
          SourceMarkedRadialConclusions μ β x Q L R δ ∧
          (∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
            SimultaneousRetentionOn μ β x Q κ C ε η L R δ') ∧
          ∃ d : SourceMaximumAllConclusions μ β x Q L R δ,
            MixedRetainedLimitsOn μ β x Q κ C ε η L R δ d.first_moments ∧
            ∀ t : ℝ, Tendsto (fun n : ℕ => mixedCriticalTailMean n μ Q
              (d.first_moments.center n+t) (Ioo L R))
                atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  obtain ⟨C,hκ,hC,hη,hηone,hcommon⟩ := mixed_onePoint_filter_count_common_witness μ h hnp hEdge hm
  refine ⟨C,hκ,hC,hη,hηone,?_⟩
  intro ε hε hεη
  obtain ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,hRatio,hRad,d,hRet⟩ := hcommon ε hε hεη
  exact ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,hRatio,hRad,
    mixed_simultaneous_retention μ h hnp hA.edge hA.width hHigh hF,d,hRet,
    mixed_all_critical_tail_limit μ h hnp hA.edge hA.contact d.first_moments⟩

private theorem pureCriticalTailMean_eq_scalar_tail (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q) (l r H : ℝ) :
    mixedCriticalTailMean n (FiniteMixture.pure p hp a ha) Q H
      (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) =
      ExpectedTailCentering.tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
        ((n+2:ℕ)*l) ((n+2:ℕ)*r)) H := by
  rw [←sourcePureTruncatedCriticalTailMean_eq_tail n p hp a ha hQ l r H]
  let K := physicalEnergyWindow (n+2) (Ici H) (Ioo ((p:ℝ)*l) ((p:ℝ)*r))
  let S := (fun e : ℝ => (n+2:ℕ)*e) ⁻¹'
    (Ici H ∩ Ioo ((n+2:ℕ)*l) ((n+2:ℕ)*r))
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hN : (0:ℝ) < (n+2:ℕ) := by positivity
  have hLine : pureScoreWindow p K = S := by
    ext e
    change (H ≤ (n+2:ℕ)*e ∧ (p:ℝ)*e ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r)) ↔
      (H ≤ (n+2:ℕ)*e ∧ (n+2:ℕ)*e ∈ Ioo ((n+2:ℕ)*l) ((n+2:ℕ)*r))
    constructor
    · intro he
      exact ⟨he.1,mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left he.2.1 hp0.le) hN,
        mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left he.2.2 hp0.le) hN⟩
    · intro he
      exact ⟨he.1,mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left he.2.1 hN.le) hp0,
        mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left he.2.2 hN.le) hp0⟩
  change (∫⁻ J, actualScoreWindowCount (n+1)
    (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
    K (fun _ _ => 1) J ∂disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree).toReal =
    (∫⁻ J, actualValueWindowCount (n+1)
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
      S (fun _ _ => 1) J ∂disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree).toReal
  congr 1
  apply lintegral_congr
  intro J
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount (n+1) p hp a ha Q K (fun _ _ => 1) J,hLine]

private theorem sphereRegularity_field_point_bound {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (J : Disorder N P) {C : ℝ}
    (hC : sourceSphereRegularity c J ≤ C) (u : Vector N) (hu : ‖u‖^2=(N:ℝ)) :
    |field c J u| ≤ C*(N:ℝ) := by
  have h0 : Continuous (field c J) := (field_contDiff c J).continuous
  have h1 : Continuous (surfaceGradient (field c J)) := by
    simpa only [Function.comp_def,id_eq] using
      (source_surfaceGradient_joint_contDiff c).continuous.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (sourceSphereHessianExtension c J) :=
    (sourceSphereHessianExtension_contDiff c J).continuous
  have h3 : Continuous (sourceSphereThirdExtension c J) := by
    simpa only [Function.comp_def,id_eq] using
      (sourceSphereThirdExtension_joint_contDiff c).continuous.comp (continuous_const.prodMk continuous_id)
  have h1n := sourceSphereNormSup_nonneg hN (surfaceGradient (field c J)) h1
  have h2n := sourceSphereNormSup_nonneg hN (sourceSphereHessianExtension c J) h2
  have h3n := sourceSphereNormSup_nonneg hN (sourceSphereThirdExtension c J) h3
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hreg : sourceSphereRegularity c J =
      sourceSphereNormSup (field c J)/(N:ℝ)+
      sourceSphereNormSup (surfaceGradient (field c J))/Real.sqrt (N:ℝ)+
      sourceSphereNormSup (sourceSphereHessianExtension c J)+
      Real.sqrt (N:ℝ)*sourceSphereNormSup (sourceSphereThirdExtension c J) := by
    unfold sourceSphereRegularity sourceSphereNormSup
    simp only [Real.norm_eq_abs]
  have hsum : sourceSphereNormSup (field c J)/(N:ℝ) ≤ C := by
    rw [hreg] at hC
    linarith [div_nonneg h1n hs.le,mul_nonneg hs.le h3n]
  have hp := sourceSphereNormSup_point_bound (field c J) h0 u hu
  simpa only [Real.norm_eq_abs] using hp.trans ((div_le_iff₀ hNr).mp hsum)

private theorem pure_compact_count_bound (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q l r g Z : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hg : 0 < g) (hlr : l ≤ r)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p:ℝ)*l)
    (hRight : (p:ℝ)*r ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∫⁻ J, actualValueWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
        (Icc l r) (fun _ _ => 1) J
        ∂disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree) ≤ 
      ENNReal.ofReal ((r-l)*C*Real.sqrt (n+2:ℕ)*
        Real.exp (-(β*x)*(l-markE (FiniteMixture.pure p hp a ha) β x Q)*(n+2:ℕ))) := by
  let μ := FiniteMixture.pure p hp a ha
  have hlength : 0 ≤ r-l := sub_nonneg.mpr hlr
  obtain ⟨_c,C,_hc,hC,hPref⟩ := actual_pure_intensity_prefactors p hp a ha h.overlap_range.1 (Z:=Z) hg
  refine ⟨C,hC,?_⟩
  intro n
  let K : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ Icc l r}
  have hK : MeasurableSet K := measurableSet_Icc.preimage
    (EuclideanSpace.proj (0:Fin 2)).continuous.measurable
  have hLine : pureScoreWindow p K = Icc l r := by ext e; rfl
  have hKR := actual_pure_count_intensity n p hp a ha h.overlap_range.1 K hK
  have hEq : (∫⁻ J, actualValueWindowCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q) (Icc l r) (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ e in Icc l r, pureCriticalIntensity n p hp a ha Q e := by
    calc
      _ = ∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
        ∂disorderLaw (n+2) μ.maxDegree := by
          apply lintegral_congr
          intro J
          simpa only [hLine] using
            (actual_pure_scoreWindowCount_eq_valueWindowCount (n+1) p hp a ha Q K
              (fun _ _ => 1) J).symm
      _ = _ := by simpa only [hLine] using hKR
  rw [hEq]
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hDensity : ∀ e ∈ Icc l r, pureCriticalIntensity n p hp a ha Q e ≤ 
      ENNReal.ofReal (C*Real.sqrt (n+2:ℕ)*
        Real.exp (-(β*x)*(l-markE μ β x Q)*(n+2:ℕ))) := by
    intro e he
    have hBand : (p:ℝ)*e ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z :=
      ⟨hLeft.trans (mul_le_mul_of_nonneg_left he.1 hp0),
        (mul_le_mul_of_nonneg_left he.2 hp0).trans hRight⟩
    apply (hPref n e hBand).2.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hLoss := sourcePureMarkedComplexity_global_linear_loss p hp a ha h e
    have hComp : pureMarkedComplexity p hp a ha Q e ≤ -(β*x)*(l-markE μ β x Q) := by
      nlinarith [mul_le_mul_of_nonneg_left he.1 hc0.le]
    have H := mul_le_mul_of_nonneg_left hComp (show (0:ℝ) ≤ (n+2:ℕ) by positivity)
    nlinarith
  calc
    _ ≤ ∫⁻ _e in Icc l r, ENNReal.ofReal (C*Real.sqrt (n+2:ℕ)*
        Real.exp (-(β*x)*(l-markE μ β x Q)*(n+2:ℕ))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with e he
      exact hDensity e he
    _ = _ := by
      simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      rw [←ENNReal.ofReal_mul (by positivity [hlength])]
      congr 1
      ring

/-- Proper-pure posterior filtering, using value/zero-gradient
conditioning and the original determinant normalization. -/
def PureFilterOn (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (β x Q κ C ε η δ : ℝ) : Prop :=
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  ∃ cp Ap cw Aw : ℝ, 0 < cp ∧ 0 < Ap ∧ 0 < cw ∧ 0 < Aw ∧
    ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
      ∀ e ∈ Icc (E-δ) (E+δ),
        let c := centerCoefficients (mixtureCoefficients μ) Q
        let ν := valueConditionedLaw c u hu e
        ν.real {J | ¬sourceSelectionEvent c κ C ε η E G J u} ≤ Ap*Real.exp (-cp*(n+2:ℕ)) ∧
        ENNReal.ofReal (1-Aw*Real.exp (-cw*(n+2:ℕ)))*
          (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤ 
            ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*sourceSelectionMark c κ C ε η E G J u ∂ν

private theorem pure_discarded_mass_le (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q κ C ε η δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hF : PureFilterOn p hp a ha β x Q κ C ε η δ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
        (∫⁻ J, actualValueWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q) I
          (sourceDiscardedMark (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G) J
            ∂disorderLaw (n+2) μ.maxDegree) ≤ 
          ENNReal.ofReal (B*Real.exp (-c*(n+2:ℕ))) *
            ∫⁻ J, actualValueWindowCount (n+1)
              (centerCoefficients (mixtureCoefficients μ) Q) I (fun _ _ => 1) J
                ∂disorderLaw (n+2) μ.maxDegree := by
  obtain ⟨cp,Ap,cw,Aw,_hcp,_hAp,hcw,hAw,hpost⟩ := hF
  have ht : Tendsto (fun n : ℕ => Aw*Real.exp (-cw*(n+2:ℕ))) atTop (𝓝 0) := by
    have H := (source_dimension_exp_tail_tendsto 2 hcw).const_mul Aw
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  refine ⟨cw,Aw,hcw,hAw,?_⟩
  filter_upwards [hpost,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn herr
  intro I hI hsub
  exact discarded_le_of_partition
    (sourceUnfilteredValueWindowCount_lintegral_lt_top (n+1) (by omega) _ h.overlap_range.1 I)
    (by positivity) herr.le
    (sourceRetainedValueWindowMean_add_discarded (n+1) (by omega) _ h.overlap_range.1 I hI κ C ε η _ _)
    (source_value_retained_window_mass_lower (n+1) (by omega) _ h.overlap_range.1 I hI κ C ε η _ _ _
      (fun u hu e he => (hn u hu e (hsub he)).2))

private theorem dimension_polynomial_absorption {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, B*(n+2:ℕ)*Real.exp (-c*(n+2:ℕ)) ≤ Real.exp (-(c/2)*(n+2:ℕ)) := by
  have hDim : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [hDim.eventually_ge_atTop
    (StrongFieldComplexity.polynomialAbsorptionThreshold B 1 (c/2))] with n hn
  have H := StrongFieldComplexity.polynomial_le_exp_of_threshold 1 hB (half_pos hc) hn
  simp only [pow_one] at H
  calc
    _ ≤ Real.exp (c/2*(n+2:ℕ))*Real.exp (-c*(n+2:ℕ)) :=
      mul_le_mul_of_nonneg_right H (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

private theorem pure_simultaneous_retention (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q κ C ε η l r δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (_hC : 0 < C) (hδ : 0 < δ)
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hF : PureFilterOn p hp a ha β x Q κ C ε η δ)
    (hreg : ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      (disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree).real
        {J | C < sourceSphereRegularity
          (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q) J} ≤ 
            A*Real.exp (-(n+2:ℕ))) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      SimultaneousRetentionOn (FiniteMixture.pure p hp a ha) β x Q κ C ε η
        ((p:ℝ)*l) ((p:ℝ)*r) δ' := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  let g := (markK μ β Q-sourceRadialEdge μ Q)/2
  have hg : 0 < g := half_pos (sub_pos.mpr (sourceContact_markK_above_edge μ h))
  obtain ⟨b,B,hb,hB,hbad⟩ := pure_discarded_mass_le p hp a ha h hF
  obtain ⟨A,hA,hregA⟩ := hreg
  let dEdge := (markK μ β Q-sourceRadialEdge μ Q)/(4*(p:ℝ))
  have hdEdge : 0 < dEdge := div_pos (sub_pos.mpr (sourceContact_markK_above_edge μ h)) (by positivity)
  let δ' := min δ (min dEdge (min ((E-l)/2) (min ((r-E)/2) (b/(2*(β*x))))))
  have hδ' : 0 < δ' := lt_min hδ (lt_min hdEdge (lt_min (by positivity [hm.1])
    (lt_min (by positivity [hm.2]) (by positivity))))
  have hδδ : δ' ≤ δ := min_le_left _ _
  have hδedge : δ' ≤ dEdge := (min_le_right _ _).trans (min_le_left _ _)
  have hδl : δ' ≤ (E-l)/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδr : δ' ≤ (r-E)/2 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hδb : δ' ≤ b/(2*(β*x)) := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hbrate : (β*x)*δ' ≤ b/2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2*(β*x))).mp hδb
    nlinarith
  let I := Icc (E-δ') (E+δ)
  let top := max C (E+δ')+1
  let T := Icc (E+δ') top
  have hLeft : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*(E-δ') :=
    source_pure_value_box_edge_margin p hp a ha h hδedge _ ⟨le_rfl,by linarith⟩
  obtain ⟨D,hD,hcoarse⟩ := pure_compact_count_bound p hp a ha h hg
    (show E-δ' ≤ E+δ by linarith) hLeft (le_refl ((p:ℝ)*(E+δ)))
  have hLeftUp : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*(E+δ') :=
    hLeft.trans (mul_le_mul_of_nonneg_left (by linarith) hp0.le)
  have htop : E+δ' < top := by dsimp [top]; linarith [le_max_right C (E+δ')]
  obtain ⟨DUp,hDUp,hcoarseUp⟩ := pure_compact_count_bound p hp a ha h hg htop.le hLeftUp
    (le_refl ((p:ℝ)*top))
  let badCount (n : ℕ) := actualValueWindowCount (n+1) cQ I (sourceDiscardedMark cQ κ C ε η E G)
  let upperCount (n : ℕ) := actualValueWindowCount (n+1) cQ T (fun _ _ => 1)
  have hbadMean : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, badCount n J ∂disorderLaw (n+2) μ.maxDegree) ≤ 
        ENNReal.ofReal (Real.exp (-(b/4)*(n+2:ℕ))) := by
    filter_upwards [hbad,dimension_polynomial_absorption
      (B:=B*((δ+δ')*D)) (by positivity) (half_pos hb)] with n hn hpoly
    have hsub : I ⊆ Icc (E-δ) (E+δ) := by
      intro e he
      exact ⟨by linarith [he.1],he.2⟩
    have hroot : Real.sqrt (n+2:ℕ) ≤ (n+2:ℕ) := Real.sqrt_le_self_iff.mpr (Or.inr (by
      exact_mod_cast (show 1 ≤ n+2 by omega)))
    apply (hn I measurableSet_Icc hsub).trans
    apply (mul_le_mul' le_rfl (hcoarse n)).trans
    rw [←ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = B*((δ+δ')*D)*Real.sqrt (n+2:ℕ)*
          Real.exp ((-b+(β*x)*δ')*(n+2:ℕ)) := by
        rw [show -(β*x)*((E-δ')-E)*(n+2:ℕ)=(β*x)*δ'*(n+2:ℕ) by ring]
        rw [show (-b+(β*x)*δ')*(n+2:ℕ)=-b*(n+2:ℕ)+(β*x)*δ'*(n+2:ℕ) by ring,
          Real.exp_add]
        ring
      _ ≤ B*((δ+δ')*D)*(n+2:ℕ)*Real.exp (-(b/2)*(n+2:ℕ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hroot (by positivity)) _ (by positivity) (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hbrate (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
      _ ≤ _ := by simpa only [show b/2/2=b/4 by ring] using hpoly
  have hupperMean : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, upperCount n J ∂disorderLaw (n+2) μ.maxDegree) ≤ 
        ENNReal.ofReal (Real.exp (-((β*x)*δ'/2)*(n+2:ℕ))) := by
    filter_upwards [dimension_polynomial_absorption
      (B:=(top-(E+δ'))*DUp) (by positivity) (mul_pos hc0 hδ')] with n hn
    apply (hcoarseUp n).trans
    apply ENNReal.ofReal_le_ofReal
    have hroot : Real.sqrt (n+2:ℕ) ≤ (n+2:ℕ) := Real.sqrt_le_self_iff.mpr (Or.inr (by
      exact_mod_cast (show 1 ≤ n+2 by omega)))
    calc
      _ = (top-(E+δ'))*DUp*Real.sqrt (n+2:ℕ)*Real.exp (-((β*x)*δ')*(n+2:ℕ)) := by congr 2; ring
      _ ≤ (top-(E+δ'))*DUp*(n+2:ℕ)*Real.exp (-((β*x)*δ')*(n+2:ℕ)) := by
        gcongr
      _ ≤ _ := hn
  let bad (n : ℕ) := toMeasurable (disorderLaw (n+2) μ.maxDegree) {J | 1 ≤ badCount n J}
  let upper (n : ℕ) := toMeasurable (disorderLaw (n+2) μ.maxDegree) {J | 1 ≤ upperCount n J}
  let reg (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) := {J | sourceSphereRegularity cQ J ≤ C}
  let Ω (n : ℕ) := (reg n ∩ (bad n)ᶜ) ∩ (upper n)ᶜ
  have hΩm (n : ℕ) : MeasurableSet (Ω n) :=
    (((isClosed_le (sourceSphereRegularity_continuous cQ) continuous_const).measurableSet).inter
      (measurableSet_toMeasurable _ _).compl).inter (measurableSet_toMeasurable _ _).compl
  have hgood : ∀ n J, J ∈ Ω n →
      sourceSphereRegularity cQ J ≤ C ∧
      (∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
        ‖sourceSphereThirdExtension cQ J u‖ ≤ C/Real.sqrt (n+2:ℕ)) ∧
      ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) → surfaceGradient (field cQ J) u=0 →
        (n+2:ℕ)*(E-δ') ≤ field cQ J u → field cQ J u ≤ (n+2:ℕ)*(E+δ') ∧
          actualScore cQ J u 1 ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r) ∧
          sourceSelectionEvent cQ κ C ε η E G J u := by
    intro n J hJ
    obtain ⟨⟨hReg,hNotBad⟩,hNotUpper⟩ := hJ
    refine ⟨hReg,fun u hu => sourceSphereRegularity_third_point_bound (by omega) cQ J hReg u hu,?_⟩
    intro u hu huc hhigh
    have hlow : E-δ' ≤ actualValue cQ J u := by
      unfold actualValue
      exact (le_div_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr (by simpa only [mul_comm] using hhigh)
    have hUp : field cQ J u ≤ (n+2:ℕ)*(E+δ') := by
      by_contra hbadUp
      apply hNotUpper
      apply subset_toMeasurable _ _
      have hwin : actualValue cQ J u ∈ T := by
        refine ⟨?_,?_⟩
        · unfold actualValue
          exact (le_div_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr (by simpa only [mul_comm] using (lt_of_not_ge hbadUp).le)
        · unfold actualValue
          apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr
          have H := (le_abs_self (field cQ J u)).trans (sphereRegularity_field_point_bound (by omega) cQ J hReg u hu)
          exact H.trans (by gcongr; dsimp [top]; linarith [le_max_left C (E+δ')])
      exact ENNReal.le_tsum (f:=fun _z : {z : Vector (n+2) | ‖z‖^2=(n+2:ℕ) ∧
        surfaceGradient (field cQ J) z=0 ∧ actualValue cQ J z ∈ T} => (1:ℝ≥0∞))
        ⟨u,hu,huc,hwin⟩
    have hup : actualValue cQ J u ≤ E+δ' := by
      unfold actualValue
      exact (div_le_iff₀ (by positivity : (0:ℝ) < (n+2:ℕ))).mpr (by simpa only [mul_comm] using hUp)
    refine ⟨hUp,?_,?_⟩
    · rw [pure_actualScore_radial_eq_value (n+2) p hp a ha Q J u]
      exact ⟨mul_lt_mul_of_pos_left (by linarith) hp0,mul_lt_mul_of_pos_left (by linarith) hp0⟩
    · by_contra hNotSel
      apply hNotBad
      apply subset_toMeasurable _ _
      have hwin : actualValue cQ J u ∈ I := ⟨hlow,hup.trans (by linarith)⟩
      have H := ENNReal.le_tsum (f:=fun z : {z : Vector (n+2) | ‖z‖^2=(n+2:ℕ) ∧
        surfaceGradient (field cQ J) z=0 ∧ actualValue cQ J z ∈ I} =>
          sourceDiscardedMark cQ κ C ε η E G J z) ⟨u,hu,huc,hwin⟩
      simpa only [sourceDiscardedMark,ite_eq_right hNotSel,badCount,actualValueWindowCount,
        mem_ofPred_eq,show n+1+1=n+2 by omega] using H
  let rate := min 1 (min (b/4) ((β*x)*δ'/2))
  have hrate : 0 < rate := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hprob : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ (A+2)*Real.exp (-rate*(n+2:ℕ)) := by
    filter_upwards [hbadMean,hupperMean] with n hn hu
    have hBm := (actual_value_window_kacRice (n+1) (by omega) μ h.overlap_range.1 I measurableSet_Icc
      (sourceDiscardedMark cQ κ C ε η E G) (sourceDiscardedMark_measurable cQ κ C ε η E G)).1
    have hUm := (actual_value_window_kacRice (n+1) (by omega) μ h.overlap_range.1 T measurableSet_Icc
      (fun _ _ => 1) measurable_const).1
    have hBprob := count_event_probability_le _ _ hBm (Real.exp_pos _).le hn
    have hUprob := count_event_probability_le _ _ hUm (Real.exp_pos _).le hu
    have hRegProb : (disorderLaw (n+2) μ.maxDegree).real (reg n)ᶜ ≤ A*Real.exp (-(n+2:ℕ)) := by
      simpa only [reg,compl_ofPred,not_le] using hregA n
    have hUnion : (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ 
        A*Real.exp (-(n+2:ℕ))+Real.exp (-(b/4)*(n+2:ℕ))+
          Real.exp (-((β*x)*δ'/2)*(n+2:ℕ)) := by
      have hsub : (Ω n)ᶜ ⊆ ((reg n)ᶜ ∪ bad n) ∪ upper n := by
        simp only [Ω,compl_inter,compl_compl]
        exact Subset.rfl
      exact (measureReal_mono hsub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add
          ((measureReal_union_le _ _).trans (add_le_add hRegProb hBprob)) hUprob))
    have hrate' {t : ℝ} (ht : rate ≤ t) : Real.exp (-t*(n+2:ℕ)) ≤ Real.exp (-rate*(n+2:ℕ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right ht (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
    apply hUnion.trans
    calc
      _ ≤ A*Real.exp (-rate*(n+2:ℕ))+Real.exp (-rate*(n+2:ℕ))+Real.exp (-rate*(n+2:ℕ)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (by simpa using hrate' (min_le_left _ _)) hA.le)
          (hrate' ((min_le_right _ _).trans (min_le_left _ _))))
            (hrate' ((min_le_right _ _).trans (min_le_right _ _)))
      _ = _ := by ring
  obtain ⟨D,hD,hAll⟩ := event_probability_all_dimensions μ Ω hrate hprob
  exact ⟨δ',hδ',hδδ,rate,D,hrate,hD,Ω,hΩm,hAll,hgood⟩

private theorem margin_mono {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (u : Vector N) {κ κ' : ℝ} (hle : κ ≤ κ') (h : sourceHessianMargin c κ' J u) :
    sourceHessianMargin c κ J u := by
  intro v
  exact (h v).trans (by nlinarith [sq_nonneg ‖tangentProjection u v‖,
    mul_le_mul_of_nonneg_right hle (sq_nonneg ‖tangentProjection u v‖)])

private theorem selectionMark_mono_margin {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) (u : Vector N) {κ κ' C ε η E G : ℝ} (hle : κ ≤ κ') :
    sourceSelectionMark c κ' C ε η E G J u ≤ sourceSelectionMark c κ C ε η E G J u := by
  unfold sourceSelectionMark
  split_ifs with h' h
  · rfl
  · exact False.elim (h ⟨margin_mono c J u hle h'.1,h'.2⟩)
  · exact zero_le
  · rfl

private theorem pure_base_filter_common (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q L₀ R₀ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hEdge : sourceRadialEdge (FiniteMixture.pure p hp a ha) Q < L₀)
    (hm : markK (FiniteMixture.pure p hp a ha) β Q∈Ioo L₀ R₀) :
    let μ := FiniteMixture.pure p hp a ha
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      (∀ n : ℕ, (disorderLaw (n+2) μ.maxDegree).real
        {J | C < sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J} ≤ 
          C*Real.exp (-(n+2:ℕ))) ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ δ : ℝ, 0 < δ ∧ δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          PureFilterOn p hp a ha β x Q κ C ε η δ := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let κ := (L₀-sourceRadialEdge μ Q)/4
  let g := (markK μ β Q-sourceRadialEdge μ Q)/2
  let M := |E|+2
  have hκ : 0 < κ := div_pos (sub_pos.mpr hEdge) (by norm_num)
  have hg : 0 < g := div_pos (sub_pos.mpr (sourceContact_markK_above_edge μ h)) (by norm_num)
  have hκg : κ ≤ g/2 := by dsimp [κ,g]; linarith [hm.1]
  obtain ⟨C₀,hC₀,hOrig⟩ := original_regularity_literal μ Q
  obtain ⟨C₁,_hC₁,hreg⟩ := source_value_physical_posterior_sphere_regularity μ h.overlap_range.1
    (show 0 ≤ M by dsimp [M]; positivity)
  let C := max C₀ C₁
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  have hregC : ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
      ∀ e : ℝ, |e| ≤ M → (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e).real
        {J | C < sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J} ≤ 
          (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2) := by
    intro n u hu e he
    let ν := valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e
    let : IsProbabilityMeasure ν := by unfold ν valueConditionedLaw; infer_instance
    exact (measureReal_mono (fun J hJ => lt_of_le_of_lt (le_max_right C₀ C₁) hJ)).trans
      (hreg n u hu e he)
  let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
  have hθ : 0 < min (Real.pi/4) (κ/(2*C)) := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ : min (Real.pi/4) (κ/(2*C)) < Real.pi/2 :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (min (Real.pi/4) (κ/(2*C))) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθπ⟩
  have hcos1 : Real.cos (min (Real.pi/4) (κ/(2*C))) < 1 := by
    have H := Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=min (Real.pi/4) (κ/(2*C)))
      (by norm_num) (by linarith [Real.pi_pos]) hθ
    simpa only [Real.cos_zero] using H
  have hη : 0 < η := sub_pos.mpr hcos1
  refine ⟨C,hκ,hC,?_,hη,by linarith,?_⟩
  · intro n
    apply ((measureReal_mono (fun J hJ => lt_of_le_of_lt (le_max_left C₀ C₁) hJ)).trans (hOrig n)).trans
    exact mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) (Real.exp_pos _).le
  intro ε hε hεη
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hG : 0 < G := (pure_source_trial_gap p hp a ha h hε hη hεη).1
  have hMBound : |E|+1+1 ≤ M := by dsimp [M]; linarith
  obtain ⟨δp,hδp,hδpG,_hδpOne,gp,_hgp,hprob⟩ :=
    source_pure_physical_posterior_selection_failure_fixed_regularity p hp a ha h hε hη hεη
      (by norm_num : (0:ℝ) < 1) hC hMBound hregC
  obtain ⟨δw,C₂,hδw,_hδwG,_hδwOne,hC₂,gw,_hgw,_herror,hweight⟩ :=
    source_pure_physical_posterior_determinant_selection_loss_fixed_regularity p hp a ha h hε hη hεη
      (by norm_num : (0:ℝ) < 1) hC hMBound hregC
  obtain ⟨cp,Ap,hcp,hAp,hprate⟩ := failure_rate_exponential μ h.overlap_range.1 hG hg gp
  obtain ⟨Aw,cw,hAw,hcw,hwrate⟩ := sourceSelectionWeightError_exponential C₂ hC₂ μ h.overlap_range.1 hG hg gw
  let δ := min δp δw
  have hδ : 0 < δ := lt_min hδp hδw
  refine ⟨δ,hδ,(min_le_left _ _).trans_lt hδpG,cp,Ap,cw,Aw,hcp,hAp,hcw,hAw,?_⟩
  filter_upwards [hprob,hweight] with n hn hw
  intro u hu e he
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let ν := valueConditionedLaw cQ u hu e
  let : IsProbabilityMeasure ν := by unfold ν valueConditionedLaw; infer_instance
  have hep : e∈Icc (E-δp) (E+δp) := by
    have H := min_le_left δp δw
    constructor <;> linarith [he.1,he.2]
  have hew : e∈Icc (E-δw) (E+δw) := by
    have H := min_le_right δp δw
    constructor <;> linarith [he.1,he.2]
  have hsub : {J : Disorder (n+2) μ.maxDegree | ¬sourceSelectionEvent cQ κ C ε η E G J u} ⊆
      {J | ¬sourceSelectionEvent cQ (g/2) C ε η E G J u} := by
    intro J hJ hs
    exact hJ ⟨margin_mono cQ J u hκg hs.1,hs.2⟩
  refine ⟨(measureReal_mono hsub).trans ((hn u hu e hep).trans (hprate n)),?_⟩
  have hmono : (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*sourceSelectionMark cQ (g/2) C ε η E G J u ∂ν) ≤ 
      ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*sourceSelectionMark cQ κ C ε η E G J u ∂ν :=
    lintegral_mono (fun J => mul_le_mul_of_nonneg_left (selectionMark_mono_margin cQ J u hκg) zero_le)
  apply le_trans _ hmono
  apply le_trans _ (hw.2 u hu e hew)
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.ofReal_le_ofReal
  change 1-Aw*Real.exp (-cw*(n+2:ℕ)) ≤ 1-sourceSelectionWeightError C₂ μ Q G g gw n
  linarith [hwrate n]

private theorem pure_inner_slope_window (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    ∃ d : ℝ, 0 < d ∧ ∀ e∈Icc
      (markE (FiniteMixture.pure p hp a ha) β x Q-d)
      (markE (FiniteMixture.pure p hp a ha) β x Q+d),
      3*(β*x)/4 ≤ -deriv (pureMarkedComplexity p hp a ha Q) e ∧
      -deriv (pureMarkedComplexity p hp a ha Q) e ≤ (3*(β*x)+β)/4 := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let B := markB μ Q
  let Δ := markK μ β Q-sourceRadialEdge μ Q
  have hΔ : 0 < Δ := sub_pos.mpr (sourceContact_markK_above_edge μ h)
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hB : 0 < B := markB_pos μ h.overlap_range.1
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hK : 2*Real.sqrt B < (p:ℝ)*E := by
    have H := sourceContact_markK_above_edge μ h
    rw [source_pure_markK_eq_degree_mul_markE p hp a ha h] at H
    exact H
  have hz : 2 < (p:ℝ)*E/Real.sqrt B := (lt_div_iff₀ hs).mpr hK
  have harg : ContinuousAt (fun e : ℝ => (p:ℝ)*e/Real.sqrt B) E := by fun_prop
  have hres : ContinuousAt
      (fun e : ℝ => SemicirclePotential.resolvent ((p:ℝ)*e/Real.sqrt B)) E :=
    (SemicirclePotential.resolvent_hasDerivAt hz).continuousAt.comp
      (f:=fun e : ℝ => (p:ℝ)*e/Real.sqrt B) harg
  have hcont : ContinuousAt (sourcePureComplexityDerivative p hp a ha Q) E := by
    change ContinuousAt (fun e : ℝ => -e/μ.xi Q+(p:ℝ)/Real.sqrt B*
      SemicirclePotential.resolvent ((p:ℝ)*e/Real.sqrt B)) E
    exact (continuousAt_id.neg.div_const _).add (continuousAt_const.mul hres)
  let slope : ℝ→ℝ := fun e => -sourcePureComplexityDerivative p hp a ha Q e
  have hcontact : slope E=β*x := by
    dsimp [slope]
    rw [sourcePure_contact_complexity_derivative p hp a ha h]
    ring
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hcβ : β*x < β := mul_lt_of_lt_one_right h.beta_pos h.weight_range.2
  have hnear : ∀ᶠ e : ℝ in 𝓝 E, slope e∈Ioo (3*(β*x)/4) ((3*(β*x)+β)/4) := by
    exact hcont.neg.tendsto.eventually
      (isOpen_Ioo.mem_nhds (by
        change slope E ∈ Ioo (3*(β*x)/4) ((3*(β*x)+β)/4)
        rw [hcontact]
        constructor <;> linarith))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d := min (r/2) (Δ/(4*(p:ℝ)))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdr : d < r := by dsimp [d]; linarith [min_le_left (r/2) (Δ/(4*(p:ℝ)))]
  have hdΔ : d ≤ Δ/(4*(p:ℝ)) := min_le_right _ _
  refine ⟨d,hd,?_⟩
  intro e he
  have hedist : dist e E < r := by
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ?_) hdr
    constructor <;> linarith [he.1,he.2]
  have hSlope := hball hedist
  have hShift := source_pure_value_box_edge_margin p hp a ha h hdΔ e he
  have hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < (p:ℝ)*e := by
    change 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) at hΔ
    linarith
  rw [(sourcePureComplexity_hasDerivAt p hp a ha h.overlap_range.1 e hEdge).deriv]
  exact ⟨hSlope.1.le,hSlope.2.le⟩

/-- All of the manuscript's pure admissibility conditions, including the
inner slope bounds on the whole closed radial interval. -/
structure PureAdmissible (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (β x Q l r δ : ℝ) : Prop where
  edge : sourceRadialEdge (FiniteMixture.pure p hp a ha) Q < (p:ℝ)*l
  contact : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r
  width : 0 < δ
  graph : ∀ e ∈ Icc (markE (FiniteMixture.pure p hp a ha) β x Q-δ)
      (markE (FiniteMixture.pure p hp a ha) β x Q+δ),
    (p:ℝ)*e ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r)
  slope : ∀ e : ℝ, (p:ℝ)*e ∈ Icc ((p:ℝ)*l) ((p:ℝ)*r) →
    3*(β*x)/4 ≤ -deriv (pureMarkedComplexity p hp a ha Q) e ∧
      -deriv (pureMarkedComplexity p hp a ha Q) e ≤ (3*(β*x)+β)/4

private theorem PureFilterOn.shrink_energy {p : ℕ} {hp : 2 ≤ p} {a : ℝ} {ha : 0 < a}
    {β x Q κ C ε η δ δ' : ℝ}
    (hF : PureFilterOn p hp a ha β x Q κ C ε η δ) (hle : δ' ≤ δ) :
    PureFilterOn p hp a ha β x Q κ C ε η δ' := by
  obtain ⟨cp,Ap,cw,Aw,hcp,hAp,hcw,hAw,hpost⟩ := hF
  refine ⟨cp,Ap,cw,Aw,hcp,hAp,hcw,hAw,?_⟩
  filter_upwards [hpost] with n hn
  intro u hu e he
  exact hn u hu e ⟨by linarith [he.1],by linarith [he.2]⟩

private theorem maximum_probability_le_critical_tail_and_localization_error
    (n : ℕ) (μ : FiniteMixture) {Q E δ H : ℝ} (hQ : 0 < Q)
    (U : Set ℝ) (hU : MeasurableSet U)
    (Ω : Set (Disorder (n+2) μ.maxDegree))
    (hΩ : ∀ J ∈ Ω, ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 →
      (n+2:ℕ)*(E-δ) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J u →
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U)
    (hH : (n+2:ℕ)*(E-δ) ≤ H) :
    (disorderLaw (n+2) μ.maxDegree).real {J | H ≤ sourceSphereMaximum n μ Q J} ≤
      mixedCriticalTailMean n μ Q H U+(disorderLaw (n+2) μ.maxDegree).real Ωᶜ := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K := physicalEnergyWindow (n+2) (Ici H) U
  let Z := actualScoreWindowCount (n+1) c K (fun _ _ => 1)
  have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _
    (measurableSet_Ici.preimage (measurable_const_mul ((n+2:ℕ):ℝ))) hU
  have hZ : AEMeasurable Z (disorderLaw (n+2) μ.maxDegree) :=
    actualScoreWindowCount_aemeasurable (n+1) (by omega) μ hQ K hK _ measurable_const
  have hsub : {J | H ≤ sourceSphereMaximum n μ Q J} ⊆ {J | 1 ≤ Z J} ∪ Ωᶜ := by
    intro J hJ
    by_cases hmem : J ∈ Ω
    · left
      obtain ⟨u,hu,hcrit,_hmax,hvalue⟩ := sourceSphereMaximum_attained n μ Q J
      change H ≤ sourceSphereMaximum n μ Q J at hJ
      rw [hvalue] at hJ
      have hr := hΩ J hmem u hu hcrit (hH.trans hJ)
      have hwin : actualScore c J u ∈ K := by
        refine ⟨?_,hr⟩
        change H ≤ (n+2:ℕ)*actualScore c J u 0
        rw [actualScore_value_eq,mul_div_cancel₀ _ (by positivity)]
        exact hJ
      exact ENNReal.le_tsum (f := fun _z : {z : Vector (n+2) |
        ‖z‖^2=(n+2:ℕ) ∧ surfaceGradient (field c J) z=0 ∧ actualScore c J z ∈ K} => (1:ℝ≥0∞))
        ⟨u,hu,hcrit,hwin⟩
    · exact Or.inr hmem
  have hMark : disorderLaw (n+2) μ.maxDegree {J | 1 ≤ Z J} ≤ mixedCriticalTailMass n μ Q H U := by
    change _ ≤ ∫⁻ J, Z J ∂disorderLaw (n+2) μ.maxDegree
    simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hZ 1
  have hMarkReal := ENNReal.toReal_mono (mixedCriticalTailMass_finite n μ hQ H U).ne hMark
  calc
    _ ≤ (disorderLaw (n+2) μ.maxDegree).real ({J | 1 ≤ Z J} ∪ Ωᶜ) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (disorderLaw (n+2) μ.maxDegree).real {J | 1 ≤ Z J}+
        (disorderLaw (n+2) μ.maxDegree).real Ωᶜ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hMarkReal le_rfl

private theorem maximum_limsup_of_allcritical_tail_and_localization
    (μ : FiniteMixture) {Q E δ c₀ M cErr CErr : ℝ}
    (hQ : 0 < Q) (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcErr : 0 < cErr) (m : ℕ → ℝ)
    (hlog : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2:ℕ)*E-Real.log (n+2:ℕ)/(2*c₀))| ≤ M)
    (U : Set ℝ) (hU : MeasurableSet U)
    (Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree))
    (hΩ : ∀ n : ℕ, ∀ J ∈ Ω n, ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 →
      (n+2:ℕ)*(E-δ) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J u →
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U)
    (hFail : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ CErr*Real.exp (-cErr*(n+2:ℕ)))
    (hTail : ∀ t : ℝ, Tendsto (fun n : ℕ => mixedCriticalTailMean n μ Q (m n+t) U)
      atTop (𝓝 (Real.exp (-c₀*t)))) :
    ∀ t : ℝ, Filter.limsup (fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
      {J | m n+t ≤ sourceSphereMaximum n μ Q J}) atTop ≤ Real.exp (-c₀*t) := by
  intro t
  have hAbove := normalized_source_center_above_lower_energy hc₀ hM hδ m hlog t
  have hDim : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-cErr*(n+2:ℕ))) atTop (𝓝 (0:ℝ)) :=
    Real.tendsto_exp_atBot.comp (hDim.const_mul_atTop_of_neg (neg_neg_of_pos hcErr))
  have hUpper : Tendsto (fun n : ℕ => mixedCriticalTailMean n μ Q (m n+t) U+
      CErr*Real.exp (-cErr*(n+2:ℕ))) atTop (𝓝 (Real.exp (-c₀*t))) := by
    simpa only [mul_zero,add_zero] using (hTail t).add (hExp.const_mul CErr)
  have hProb : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real {J | m n+t ≤ sourceSphereMaximum n μ Q J} ≤
        mixedCriticalTailMean n μ Q (m n+t) U+CErr*Real.exp (-cErr*(n+2:ℕ)) := by
    filter_upwards [hFail,hAbove] with n hn hhigh
    exact (maximum_probability_le_critical_tail_and_localization_error n μ hQ U hU
      (Ω n) (hΩ n) hhigh).trans (add_le_add le_rfl hn)
  have hCobounded := isCoboundedUnder_le_of_le atTop
    (fun n : ℕ => measureReal_nonneg (μ := disorderLaw (n+2) μ.maxDegree)
      (s := {J | m n+t ≤ sourceSphereMaximum n μ Q J}))
  exact (limsup_le_limsup hProb hCobounded hUpper.isBoundedUnder_le).trans_eq hUpper.limsup_eq

def pureCenteredValueWindow (n : ℕ) (m : ℕ→ℝ) (l r A B : ℝ) : Set ℝ :=
  (fun e : ℝ => (n+2:ℕ)*e) ⁻¹'
    (Icc (m n+A) (m n+B) ∩ Ioo ((n+2:ℕ)*l) ((n+2:ℕ)*r))

def pureCenteredValueTail (n : ℕ) (m : ℕ→ℝ) (l r t : ℝ) : Set ℝ :=
  (fun e : ℝ => (n+2:ℕ)*e) ⁻¹'
    (Ici (m n+t) ∩ Ioo ((n+2:ℕ)*l) ((n+2:ℕ)*r))

def PureRetainedLimitsOn (p : ℕ) (hp : 2≤p) (a : ℝ) (ha : 0<a)
    (β x Q κ C ε η l r δ : ℝ) (d : PureScalarNormalization p hp a ha β x Q l r) : Prop :=
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  (∀ A B : ℝ, A≤B → Tendsto (fun n : ℕ => sourceRetainedValueWindowMean (n+1) μ Q
    (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)) κ C ε η E G)
    atTop (𝓝 (Real.exp (-(β*x)*A)-Real.exp (-(β*x)*B)))) ∧
  (∀ t : ℝ, Tendsto (fun n : ℕ => sourceRetainedValueWindowMean (n+1) μ Q
    (pureCenteredValueTail n d.center l r t ∩ Icc (E-δ) (E+δ)) κ C ε η E G)
    atTop (𝓝 (Real.exp (-(β*x)*t))))

private theorem pure_retained_limits_of_filter (p : ℕ) (hp : 2≤p) (a : ℝ) (ha : 0<a)
    {β x Q κ C ε η l r δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hδ : 0<δ) (hF : PureFilterOn p hp a ha β x Q κ C ε η δ)
    (d : PureScalarNormalization p hp a ha β x Q l r) :
    PureRetainedLimitsOn p hp a ha β x Q κ C ε η l r δ d := by
  dsimp only [PureRetainedLimitsOn]
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hc : 0<β*x := mul_pos h.beta_pos h.weight_range.1
  have hlog : ∀ᶠ n : ℕ in atTop,
      |d.center n-((n+2:ℕ)*E-Real.log (n+2:ℕ)/(2*(β*x)))| ≤ d.log_constant := by
    filter_upwards [eventually_ge_atTop d.cutoff] with n hn
    exact (d.normalization n hn).2.2
  obtain ⟨_cp,_Ap,cw,Aw,_hcp,_hAp,hcw,_hAw,hpost⟩ := hF
  let error : ℕ→ℝ := fun n => Aw*Real.exp (-cw*(n+2:ℕ))
  have herror : Tendsto error atTop (𝓝 (0:ℝ)) := by
    have H := (source_dimension_exp_tail_tendsto 2 hcw).const_mul Aw
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  have hwindow : ∀ A B : ℝ, A≤B → Tendsto (fun n : ℕ => sourceRetainedValueWindowMean (n+1) μ Q
      (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)) κ C ε η E G)
      atTop (𝓝 (Real.exp (-(β*x)*A)-Real.exp (-(β*x)*B))) := by
    intro A B hAB
    have hall : Tendsto (fun n : ℕ => sourceUnfilteredValueWindowMean (n+1) μ Q
        (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)))
        atTop (𝓝 (Real.exp (-(β*x)*A)-Real.exp (-(β*x)*B))) := by
      apply (d.critical_window A B hAB).congr'
      filter_upwards [source_logarithmic_center_offset_bounds hc d.log_constant_pos.le hδ
        d.center hlog A B] with n hn
      have hsub : pureCenteredValueWindow n d.center l r A B ⊆ Icc (E-δ) (E+δ) := by
        intro e he
        have hN : (0:ℝ)<(n+2:ℕ) := by positivity
        change ((d.center n+A ≤ (n+2:ℕ)*e ∧ (n+2:ℕ)*e ≤ d.center n+B) ∧
          (n+2:ℕ)*l < (n+2:ℕ)*e ∧ (n+2:ℕ)*e < (n+2:ℕ)*r) at he
        exact ⟨(mul_le_mul_iff_right₀ hN).mp (hn.1.trans he.1.1),
          (mul_le_mul_iff_right₀ hN).mp (he.1.2.trans hn.2)⟩
      change sourceUnfilteredValueWindowMean (n+1) μ Q
        (pureCenteredValueWindow n d.center l r A B) = _
      rw [inter_eq_left.mpr hsub]
    have hlo : Tendsto (fun n : ℕ => (1-error n)*sourceUnfilteredValueWindowMean (n+1) μ Q
        (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)))
        atTop (𝓝 (Real.exp (-(β*x)*A)-Real.exp (-(β*x)*B))) := by
      have hOne : Tendsto (fun _n : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [sub_zero,one_mul] using (hOne.sub herror).mul hall
    have hbound : ∀ᶠ n : ℕ in atTop,
        (1-error n)*sourceUnfilteredValueWindowMean (n+1) μ Q
          (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)) ≤
          sourceRetainedValueWindowMean (n+1) μ Q
            (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)) κ C ε η E G ∧
        sourceRetainedValueWindowMean (n+1) μ Q
          (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)) κ C ε η E G ≤
          sourceUnfilteredValueWindowMean (n+1) μ Q
            (pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)) := by
      filter_upwards [hpost,herror.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn herr
      let I := pureCenteredValueWindow n d.center l r A B ∩ Icc (E-δ) (E+δ)
      have hI : MeasurableSet I :=
        ((measurableSet_Icc.inter measurableSet_Ioo).preimage
          (measurable_const_mul ((n+2:ℕ):ℝ))).inter measurableSet_Icc
      exact source_value_retained_window_mean_bounds (n+1) (by omega) μ h.overlap_range.1 I hI
        κ C ε η E G (error n) herr.le (by
          intro u hu e he
          exact (hn u hu e he.2).2)
    exact hlo.squeeze' hall (hbound.mono fun _ hn => hn.1) (hbound.mono fun _ hn => hn.2)
  refine ⟨hwindow,?_⟩
  intro t
  let A : ℕ→ℝ := fun n => sourceRetainedValueWindowMean (n+1) μ Q
    (pureCenteredValueTail n d.center l r t ∩ Icc (E-δ) (E+δ)) κ C ε η E G
  let B : ℕ→ℝ := fun n => sourceUnfilteredValueWindowMean (n+1) μ Q
    (pureCenteredValueTail n d.center l r t)
  let W : ℝ→ℕ→ℝ := fun R n => sourceRetainedValueWindowMean (n+1) μ Q
    (pureCenteredValueWindow n d.center l r t R ∩ Icc (E-δ) (E+δ)) κ C ε η E G
  have hB : Tendsto B atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    apply (d.critical_tail t).congr'
    filter_upwards [] with n
    exact (sourcePureTruncatedCriticalTailMean_eq_tail n p hp a ha h.overlap_range.1 l r
      (d.center n+t)).symm
  have hW : ∀ R : ℝ, t≤R → Tendsto (W R) atTop
      (𝓝 (Real.exp (-(β*x)*t)-Real.exp (-(β*x)*R))) := fun R hR => hwindow t R hR
  have hbound : ∀ n : ℕ, ∀ R : ℝ, t≤R → W R n≤A n ∧ A n≤B n := by
    intro n R _hR
    constructor
    · apply sourceRetainedValueWindowMean_mono (n+1) (by omega) μ h.overlap_range.1
        _ _ _ κ C ε η E G
      intro e he
      exact ⟨⟨he.1.1.1,he.1.2⟩,he.2⟩
    · apply le_trans (sourceRetainedValueWindowMean_mono (n+1) (by omega) μ h.overlap_range.1
        _ _ inter_subset_left κ C ε η E G)
      exact sourceRetainedValueWindowMean_le_unfiltered (n+1) (by omega) μ h.overlap_range.1
        _ κ C ε η E G
  exact retained_tail_tendsto_of_window_limits (β*x) t hc A B W hB hW hbound

private theorem truncated_log_shift {f : ℝ → ℝ} {L R c m H v : ℝ}
    (hc : 0 < c) (h0 : ∀ t, 0 ≤ f t)
    (hzero : ∀ t, t ∉ Ioo L R → f t = 0)
    (hpos : ∀ t ∈ Ioo L R, 0 < f t)
    (hd : ∀ t ∈ Ioo L R, deriv (fun s => Real.log (f s)) t ≤ -c)
    (hm : L < m) (hH : m ≤ H) (hv : 0 ≤ v) :
    f (H+v) ≤ f H*Real.exp (-c*v) := by
  by_cases hy : H+v ∈ Ioo L R
  · have hx : H ∈ Ioo L R := ⟨hm.trans_le hH,by linarith [hy.2]⟩
    let g : ℝ → ℝ := fun t => Real.log (f t)
    have hsub : Icc H (H+v) ⊆ Ioo L R := by
      intro t ht
      exact ⟨hx.1.trans_le ht.1,ht.2.trans_lt hy.2⟩
    have hdiff (t : ℝ) (ht : t ∈ Icc H (H+v)) : DifferentiableAt ℝ g t :=
      differentiableAt_of_deriv_ne_zero (ne_of_lt ((hd t (hsub ht)).trans_lt (neg_neg_of_pos hc)))
    have hcont : ContinuousOn g (Icc H (H+v)) :=
      fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
    have hwithin : DifferentiableOn ℝ g (interior (Icc H (H+v))) :=
      fun t ht => (hdiff t (interior_subset ht)).differentiableWithinAt
    have hle := (convex_Icc H (H+v)).image_sub_le_mul_sub_of_deriv_le
      hcont hwithin (fun t ht => hd t (hsub (interior_subset ht)))
      H ⟨le_rfl,by linarith⟩ (H+v) ⟨by linarith,le_rfl⟩ (by linarith)
    have hExp := Real.exp_le_exp.mpr (show g (H+v) ≤ g H+(-c*v) by linarith)
    simpa only [g,Real.exp_add,Real.exp_log (hpos _ hy),Real.exp_log (hpos _ hx)] using hExp
  · rw [hzero _ hy]
    exact mul_nonneg (h0 H) (Real.exp_pos _).le

private theorem pure_microscopic_envelopes (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q l r δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hA : PureAdmissible p hp a ha β x Q l r δ)
    (hEst : PureScalarEstimates p hp a ha β x Q l r)
    (d : PureScalarNormalization p hp a ha β x Q l r) :
    (∀ᶠ n : ℕ in atTop, ∀ v : ℝ, 0 ≤ v →
      ExpectedTailCentering.tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2:ℕ)*l) ((n+2:ℕ)*r)) (d.center n+v) ≤ Real.exp (-((β*x)/2)*v)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ v : ℝ, 0 ≤ v →
      pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r) (d.center n-v) ≤
        C*Real.exp (((β*x+β)/2)*v)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r)
  let g := ((p:ℝ)*l-sourceRadialEdge μ Q)/2
  have hg : 0 < g := half_pos (sub_pos.mpr hA.edge)
  have hLeft : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*l := by
    dsimp [g,sourceRadialEdge] at *
    linarith [hA.edge]
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hlog : ∀ᶠ n : ℕ in atTop,
      |d.center n-((n+2:ℕ)*E-Real.log (n+2:ℕ)/(2*(β*x)))| ≤ d.log_constant := by
    filter_upwards [eventually_ge_atTop d.cutoff] with n hn
    exact (d.normalization n hn).2.2
  constructor
  · obtain ⟨A,_hApos,hRate⟩ := hEst.log_slope
    have hsmall : ∀ᶠ n : ℕ in atTop, A/(n+2:ℕ) ≤ (β*x)/4 := by
      have H := (constant_div_dimension_tendsto A).eventually
        (gt_mem_nhds (by positivity : (0:ℝ) < (β*x)/4))
      simpa only [Nat.cast_add,Nat.cast_ofNat] using H.mono (fun _ hn => hn.le)
    have hAbove := normalized_source_center_above_lower_energy hc0 d.log_constant_pos.le
      (half_pos (sub_pos.mpr hA.contact.1)) d.center hlog 0
    filter_upwards [hRate,hsmall,hAbove,eventually_ge_atTop d.cutoff,
      pureTruncatedLocalMaxDensity_integrable_eventually p hp a ha h
        (hA.contact.1.trans hA.contact.2) hg hLeft (le_refl ((p:ℝ)*r)),
      pureTruncatedLocalMaxDensity_pos_eventually p hp a ha h hg hLeft (le_refl ((p:ℝ)*r))]
        with n hn hsmalln hAboveN hcut hi hpos
    have hN : (0:ℝ) < (n+2:ℕ) := by positivity
    have hmLower : (n+2:ℕ)*l < d.center n := by
      have H := mul_lt_mul_of_pos_left hA.contact.1 hN
      dsimp [E] at hAboveN
      nlinarith
    have hderiv : ∀ H ∈ Ioo ((n+2:ℕ)*l) ((n+2:ℕ)*r),
        deriv (fun t => Real.log (f n t)) H ≤ -((β*x)/2) := by
      intro H hH
      have he : H/(n+2:ℕ) ∈ Ioo l r :=
        ⟨(lt_div_iff₀ hN).mpr (by nlinarith [hH.1]),
          (div_lt_iff₀ hN).mpr (by nlinarith [hH.2])⟩
      have hmark : (p:ℝ)*H/(n+2:ℕ) ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r) := by
        rw [mul_div_assoc]
        exact ⟨mul_lt_mul_of_pos_left he.1 hp0,mul_lt_mul_of_pos_left he.2 hp0⟩
      have hrateN := hn H hmark
      have hSlope := hA.slope (H/(n+2:ℕ))
        ⟨mul_le_mul_of_nonneg_left he.1.le hp0.le,mul_le_mul_of_nonneg_left he.2.le hp0.le⟩
      have hfun : (fun t => Real.log (pureGraphMaximumIntensity n p hp a ha Q
          (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) t).toReal) = (fun t => Real.log (f n t)) := by
        funext t
        rw [pureGraphMaximumIntensity_eq_truncated n p hp a ha Q l r t]
      rw [hfun] at hrateN
      linarith [(abs_le.mp hrateN).2]
    intro v hv
    have ht := ExpectedTailCentering.tail_decay_of_density_envelope hi hv (fun H hH =>
      truncated_log_shift (half_pos hc0)
        (fun t => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ t)
        (fun t ht => by simp only [pureTruncatedLocalMaxDensity,indicator_of_notMem ht])
        hpos hderiv hmLower hH hv)
    simpa only [(d.normalization n hcut).1,one_mul] using ht
  · obtain ⟨A,hApos,hupper⟩ := sourcePure_truncatedLocalMax_global_upper p hp a ha h hg hLeft
      (le_refl ((p:ℝ)*r))
    refine ⟨A*Real.exp ((β*x)*d.log_constant),by positivity,?_⟩
    filter_upwards [hupper,eventually_ge_atTop d.cutoff] with n hn hcut
    intro v hv
    let N : ℝ := (n+2:ℕ)
    let t := d.center n-(N*E-Real.log N/(2*(β*x)))
    have ht : |t| ≤ d.log_constant := (d.normalization n hcut).2.2
    have hN : 0 < N := by dsimp [N]; positivity
    have hscale : Real.exp ((β*x)*(N*E-d.center n))/Real.sqrt N = Real.exp (-(β*x)*t) := by
      have hexp : (β*x)*(N*E-d.center n) = -(β*x)*(-Real.log N/(2*(β*x))+t) := by
        dsimp [t]
        ring
      rw [hexp]
      exact ExpectedTailCentering.reference_scale hN hc0 t
    have htExp : Real.exp (-(β*x)*t) ≤ Real.exp ((β*x)*d.log_constant) :=
      Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp ht).1])
    have hcβ : β*x < β := mul_lt_of_lt_one_right h.beta_pos h.weight_range.2
    calc
      f n (d.center n-v) ≤ A*Real.exp (-(β*x)*((d.center n-v)-N*E))/Real.sqrt N := hn _
      _ = A*(Real.exp ((β*x)*(N*E-d.center n))/Real.sqrt N)*Real.exp ((β*x)*v) := by
        rw [show -(β*x)*((d.center n-v)-N*E)=(β*x)*(N*E-d.center n)+(β*x)*v by ring,Real.exp_add]
        ring
      _ ≤ (A*Real.exp ((β*x)*d.log_constant))*Real.exp (((β*x+β)/2)*v) := by
        rw [hscale]
        apply mul_le_mul (mul_le_mul_of_nonneg_left htExp hApos.le) _ (by positivity) (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hcβ.le hv]

def PureDeterminantLossOn (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (β x Q κ C ε η δ : ℝ) : Prop :=
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ), ∀ e ∈ Icc (E-δ) (E+δ),
      let cQ := centerCoefficients (mixtureCoefficients μ) Q
      let ν := valueConditionedLaw cQ u hu e
      (∫ J in {J | ¬sourceSelectionEvent cQ κ C ε η E G J u}, intrinsicDet μ Q u J ∂ν) ≤
        B*Real.exp (-c*(n+2:ℕ))*(∫ J, intrinsicDet μ Q u J ∂ν)

private theorem pure_determinant_loss_of_filter (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q κ C ε η δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hF : PureFilterOn p hp a ha β x Q κ C ε η δ) :
    PureDeterminantLossOn p hp a ha β x Q κ C ε η δ := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  obtain ⟨_cp,_Ap,cw,Aw,_hcp,_hAp,hcw,hAw,hpost⟩ := hF
  have ht : Tendsto (fun n : ℕ => Aw*Real.exp (-cw*(n+2:ℕ))) atTop (𝓝 0) := by
    have H := (source_dimension_exp_tail_tendsto 2 hcw).const_mul Aw
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  refine ⟨Aw,cw,hAw,hcw,?_⟩
  filter_upwards [hpost,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn herr
  intro u hu e he
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let ν := valueConditionedLaw cQ u hu e
  let D := intrinsicDet μ Q u
  let S := {J : Disorder (n+2) μ.maxDegree | ¬sourceSelectionEvent cQ κ C ε η E G J u}
  have hDm : Measurable (fun J => ENNReal.ofReal (D J)) := intrinsicDet_measurable cQ u hu
  have hMean : (∫⁻ J, ENNReal.ofReal (D J) ∂ν) = ENNReal.ofReal
      (GOEPhysicalPotential.physicalMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e)) :=
    pure_posterior_det_mean n p hp a ha h.overlap_range.1 u hu e
  have hFin : (∫⁻ J, ENNReal.ofReal (D J) ∂ν) ≠ ⊤ := by
    rw [hMean]
    exact ENNReal.ofReal_ne_top
  have hD : Integrable D ν := by
    have H := integrable_toReal_of_lintegral_ne_top hDm.aemeasurable hFin
    convert H using 1
    funext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hpair : Measurable (fun J : Disorder (n+2) μ.maxDegree => (J,u)) :=
    measurable_id.prodMk measurable_const
  have hS : MeasurableSet S := by
    change MeasurableSet ((fun J : Disorder (n+2) μ.maxDegree => (J,u)) ⁻¹'
      {z : Disorder (n+2) μ.maxDegree × Vector (n+2) | ¬sourceSelectionEvent cQ κ C ε η E G z.1 z.2})
    exact (sourceSelectionEvent_measurable (N:=n+2) (P:=μ.maxDegree) cQ κ C ε η E G).compl.preimage hpair
  have hT : (∫⁻ J, ENNReal.ofReal (D J) ∂ν) = ENNReal.ofReal (∫ J, D J ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hD (.of_forall (fun _ => abs_nonneg _))).symm
  have hfunB : (fun J => ENNReal.ofReal (D J)*sourceDiscardedMark cQ κ C ε η E G J u) =
      S.indicator (fun J => ENNReal.ofReal (D J)) := by
    funext J
    by_cases hs : J ∈ S
    · rw [indicator_of_mem hs,sourceDiscardedMark,
        ite_eq_right (show ¬sourceSelectionEvent cQ κ C ε η E G J u from hs),mul_one]
    · rw [indicator_of_notMem hs,sourceDiscardedMark,
        ite_eq_left (show sourceSelectionEvent cQ κ C ε η E G J u from not_not.mp hs),mul_zero]
  have hB : (∫⁻ J, ENNReal.ofReal (D J)*sourceDiscardedMark cQ κ C ε η E G J u ∂ν) =
      ENNReal.ofReal (∫ J in S, D J ∂ν) := by
    rw [hfunB,lintegral_indicator hS]
    exact (ofReal_integral_eq_lintegral_ofReal hD.restrict (.of_forall (fun _ => abs_nonneg _))).symm
  have hfunR : (fun J => ENNReal.ofReal (D J)*sourceSelectionMark cQ κ C ε η E G J u) =
      Sᶜ.indicator (fun J => ENNReal.ofReal (D J)) := by
    funext J
    by_cases hs : J ∈ S
    · rw [indicator_of_notMem (show J ∉ Sᶜ from not_not.mpr hs)]
      rw [sourceSelectionMark,ite_eq_right (show ¬sourceSelectionEvent cQ κ C ε η E G J u from hs),mul_zero]
    · rw [indicator_of_mem (show J ∈ Sᶜ from hs)]
      rw [sourceSelectionMark,ite_eq_left (show sourceSelectionEvent cQ κ C ε η E G J u from not_not.mp hs),mul_one]
  have hpart : (∫⁻ J, ENNReal.ofReal (D J)*sourceSelectionMark cQ κ C ε η E G J u ∂ν)+
      (∫⁻ J, ENNReal.ofReal (D J)*sourceDiscardedMark cQ κ C ε η E G J u ∂ν) =
        ∫⁻ J, ENNReal.ofReal (D J) ∂ν := by
    rw [hfunR,hfunB,lintegral_indicator hS.compl,lintegral_indicator hS,add_comm]
    exact lintegral_add_compl _ hS
  have hfinite : (∫⁻ J, ENNReal.ofReal (D J) ∂ν) < ⊤ := by
    rw [hT]
    exact ENNReal.ofReal_lt_top
  have H := discarded_le_of_partition hfinite (by positivity) herr.le hpart (hn u hu e he).2
  rw [hB,hT,←ENNReal.ofReal_mul (by positivity)] at H
  have hden0 : 0 ≤ ∫ J, D J ∂ν := integral_nonneg (fun _ => abs_nonneg _)
  have herr0 : 0 ≤ Aw*Real.exp (-cw*(n+2:ℕ)) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg herr0 hden0)).mp H

/-- Exact mixed marked measures, density estimates and Palm formulas in
`cor:mo-interface(i)`, including arbitrary Borel whole-field weights. -/
structure MixedPointMeasuresOn (μ : FiniteMixture) (Q L R : ℝ) : Prop where
  joint_density_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ e k : ℝ, k ∈ Icc L R →
      ENNReal.ofReal (c*Real.exp ((n+2:ℕ)*markedComplexity μ Q (scorePairEquiv (e,k)))) ≤
        mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ∧
      mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ≤ mixedCriticalPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ∧
      mixedCriticalPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ≤
        ENNReal.ofReal (C*Real.exp ((n+2:ℕ)*markedComplexity μ Q (scorePairEquiv (e,k))))
  raw_counts : ∀ n : ℕ, ∀ A : Set (ℝ×ℝ), MeasurableSet A →
    ∀ ψ : Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ≥0∞,
    Measurable (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) => ψ z.1 z.2) →
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let K := {b : EuclideanSpace ℝ (Fin 2) | ((n+2:ℕ)*b 0,b 1) ∈ A}
    AEMeasurable (actualScoreWindowCount (n+1) c K ψ) (disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualScoreWindowCount (n+1) c K ψ J ∂disorderLaw (n+2) μ.maxDegree) =
        ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
          ∫⁻ z in A, ENNReal.ofReal (mathfrakC n μ Q*
            Real.exp (-(n+2:ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (z.1/(n+2:ℕ),z.2)))) *
              (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| * ψ J u
                ∂mixedConditionedLaw c u hu (scorePairEquiv (z.1/(n+2:ℕ),z.2)))
                  ∂StrongFieldComplexity.planeVolume
        else 0 ∂sphereLaw (n+2)
  palm : ∀ n : ℕ, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
    IsMarkovKernel (mixedMaximumPalmKernel n μ Q u hu (Ioo L R)) ∧
      ∀ e : ℝ, ∀ f : Disorder (n+2) μ.maxDegree × ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ w, f w ∂mixedMaximumPalmKernel n μ Q u hu (Ioo L R) e) =
          maximumPalmExpectation n μ Q u hu e (Ioo L R) (fun J k => f (J,k))
  disintegration : ∀ n : ℕ, ∀ B : Set ℝ, MeasurableSet B →
    ∀ ψ : Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ≥0∞,
    Measurable (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) => ψ z.1 z.2) →
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c (physicalEnergyWindow (n+2) B (Ioo L R))
      (fun J u => negativeHessianMark (n+1) c J u*ψ J u) J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
        ∫⁻ H in B, ENNReal.ofReal (sourceMaximumEnergyDensity n μ Q (Ioo L R) H)*
          (∫⁻ z, ψ z.1 u ∂mixedMaximumPalmKernel n μ Q u hu (Ioo L R) (H/(n+2:ℕ)))
      else 0 ∂sphereLaw (n+2)

private theorem mixed_point_measures (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hA : Admissible μ β x Q L R δ) : MixedPointMeasuresOn μ Q L R := by
  exact ⟨(intensity_bounds_literal μ h hnp hA.edge hA.contact hA.excluded).1,
    fun n A hA ψ hψ => marked_raw_kacRice n μ h.overlap_range.1 hnp A hA ψ hψ,
    fun n u hu => mixedMaximumPalmKernel_probability_and_formula n μ h hnp hA.edge hA.contact u hu,
    fun n B hB ψ hψ => mixed_weighted_maximum_palm_disintegration n μ h hnp hA.edge hA.contact B hB ψ hψ⟩

/-- The singular graph measures and proper pure Palm formulas in
`cor:mo-interface(i)`, on the same literal coefficient field. -/
structure PurePointMeasuresOn (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q l r : ℝ) : Prop where
  raw_counts : ∀ n : ℕ, ∀ A : Set (ℝ×ℝ), MeasurableSet A →
    ∀ ψ : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree → Vector (n+2) → ℝ≥0∞,
    Measurable (fun z : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × Vector (n+2) => ψ z.1 z.2) →
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A) ψ) (disorderLaw (n+2) μ.maxDegree) ∧
    (∫⁻ J, actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A) ψ J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
        ∫⁻ H in purePhysicalGraph n p ⁻¹' A, purePhysicalCoefficient n μ Q H *
          (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| * ψ J u
            ∂valueConditionedLaw c u hu (H/(n+2:ℕ)))
      else 0 ∂sphereLaw (n+2)
  palm : ∀ n : ℕ, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
    ∀ e : ℝ, (p:ℝ)*e ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r) →
      pureMaximumPalmKernel n p hp a ha Q u hu e = pureMaximumPalm n p hp a ha Q e u hu ∧
        IsProbabilityMeasure (pureMaximumPalmKernel n p hp a ha Q u hu e)
  disintegration : ∀ n : ℕ, ∀ A : Set (ℝ×ℝ), MeasurableSet A → (∀ z ∈ A, 0 < z.2) →
    ∀ ψ : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree → Vector (n+2) → ℝ≥0∞,
    Measurable (fun z : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × Vector (n+2) => ψ z.1 z.2) →
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A)
      (fun J u => negativeHessianMark (n+1) c J u*ψ J u) J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
        ∫⁻ H in purePhysicalGraph n p ⁻¹' A, pureLocalMaxPhysicalIntensity n p hp a ha Q H *
          (∫⁻ z, ψ z.1 u ∂pureMaximumPalmKernel n p hp a ha Q u hu (H/(n+2:ℕ)))
      else 0 ∂sphereLaw (n+2)

private theorem pure_point_measures (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q l r δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hA : PureAdmissible p hp a ha β x Q l r δ) : PurePointMeasuresOn p hp a ha Q l r := by
  refine ⟨fun n A hA ψ hψ => pure_marked_raw_kacRice n p hp a ha h.overlap_range.1 A hA ψ hψ,?_,
    fun n A hA hpos ψ hψ => pure_weighted_maximum_palm_disintegration n p hp a ha
      h.overlap_range.1 A hA hpos ψ hψ⟩
  intro n u hu e he
  have hzero : 0 ≤ sourceRadialEdge (FiniteMixture.pure p hp a ha) Q := by unfold sourceRadialEdge; positivity
  exact pureMaximumPalmKernel_eq_and_probability n p hp a ha h.overlap_range.1 u hu e
    (hzero.trans_lt (hA.edge.trans he.1))

/-- The pure branch of the common one-point corollary, on one fixed radial
interval, one coarse width, one selection event and one actual unit-tail
center. Counts and densities use the Euler graph, never a mixed inverse. -/
structure PureOnePointConclusions (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (β x Q κ C ε η l r δ : ℝ) where
  admissible : PureAdmissible p hp a ha β x Q l r δ
  scalar : PureScalarEstimates p hp a ha β x Q l r
  point_measures : PurePointMeasuresOn p hp a ha Q l r
  first_moments : PureScalarNormalization p hp a ha β x Q l r
  filter : PureFilterOn p hp a ha β x Q κ C ε η δ
  determinant_loss : PureDeterminantLossOn p hp a ha β x Q κ C ε η δ
  localization : AllHighOn (FiniteMixture.pure p hp a ha) β x Q κ C ((p:ℝ)*l) ((p:ℝ)*r) δ
  simultaneous_retention : SimultaneousRetentionOn (FiniteMixture.pure p hp a ha) β x Q κ C ε η
    ((p:ℝ)*l) ((p:ℝ)*r) δ
  retained_limits : PureRetainedLimitsOn p hp a ha β x Q κ C ε η l r δ first_moments
  critical_tail : ∀ t : ℝ, Tendsto (fun n : ℕ => mixedCriticalTailMean n (FiniteMixture.pure p hp a ha)
    Q (first_moments.center n+t) (Ioo ((p:ℝ)*l) ((p:ℝ)*r))) atTop (𝓝 (Real.exp (-(β*x)*t)))
  maximum_probability_limsup : ∀ t : ℝ,
    Filter.limsup (fun n : ℕ => (disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree).real
      {J | first_moments.center n+t ≤ sourceSphereMaximum n (FiniteMixture.pure p hp a ha) Q J}) atTop ≤
        Real.exp (-(β*x)*t)
  uniform_window_bound : ∀ A B : ℝ, A ≤ B → ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
    sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (first_moments.center n+A)
      (first_moments.center n+B) ≤ D ∧
    sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r (first_moments.center n+A)
      (first_moments.center n+B) ≤ D
  upper_tail_envelope : ∀ᶠ n : ℕ in atTop, ∀ v : ℝ, 0 ≤ v →
    ExpectedTailCentering.tail (pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2:ℕ)*l) ((n+2:ℕ)*r)) (first_moments.center n+v) ≤ Real.exp (-((β*x)/2)*v)
  lower_density_envelope : ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ v : ℝ, 0 ≤ v →
    pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r)
      (first_moments.center n-v) ≤ D*Real.exp (((β*x+β)/2)*v)
  lower_density_rate_lt_beta : (β*x+β)/2 < β

/-- The complete common pure localization/filter/count witness. The base
constants precede ε, the radial interval precedes every fixed window, and
the all-critical and retained unbounded tails share the exact center. -/
theorem pure_onePoint_interface (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q L₀ R₀ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hEdge : sourceRadialEdge (FiniteMixture.pure p hp a ha) Q < L₀)
    (hm : markK (FiniteMixture.pure p hp a ha) β Q ∈ Ioo L₀ R₀) :
    let μ := FiniteMixture.pure p hp a ha
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ l r δ : ℝ, L₀ < (p:ℝ)*l ∧ (p:ℝ)*r < R₀ ∧
          δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          Nonempty (PureOnePointConclusions p hp a ha β x Q κ C ε η l r δ) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let K := markK μ β Q
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hKE : K=(p:ℝ)*E := source_pure_markK_eq_degree_mul_markE p hp a ha h
  obtain ⟨C,hκ,hC,hreg,hη,hηone,hFilter⟩ := pure_base_filter_common p hp a ha h hEdge hm
  refine ⟨C,hκ,hC,hη,hηone,?_⟩
  intro ε hε hεη
  obtain ⟨s,hs,hSlope⟩ := pure_inner_slope_window p hp a ha h
  obtain ⟨δf,hδf,hδfG,hF⟩ := hFilter ε hε hεη
  let w := min (s/2) (min ((K-L₀)/(2*(p:ℝ))) ((R₀-K)/(2*(p:ℝ))))
  have hw : 0 < w := lt_min (by positivity) (lt_min (by positivity [hm.1]) (by positivity [hm.2]))
  have hws : w ≤ s := (min_le_left _ _).trans (by linarith)
  have hwL : (p:ℝ)*w ≤ (K-L₀)/2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2*(p:ℝ))).mp
      ((min_le_right _ _).trans (min_le_left _ _) : w ≤ (K-L₀)/(2*(p:ℝ)))
    nlinarith
  have hwR : (p:ℝ)*w ≤ (R₀-K)/2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2*(p:ℝ))).mp
      ((min_le_right _ _).trans (min_le_right _ _) : w ≤ (R₀-K)/(2*(p:ℝ)))
    nlinarith
  let l := E-w
  let r := E+w
  have hL : L₀ < (p:ℝ)*l := by dsimp [l]; nlinarith [hm.1]
  have hR : (p:ℝ)*r < R₀ := by dsimp [r]; nlinarith [hm.2]
  have hcontact : E ∈ Ioo l r := by constructor <;> dsimp [l,r] <;> linarith
  let δb := min δf (w/2)
  have hδb : 0 < δb := lt_min hδf (by positivity)
  have hFb := hF.shrink_energy (min_le_left δf (w/2))
  obtain ⟨δ,hδ,hδle,hSim⟩ := pure_simultaneous_retention p hp a ha h hC hδb hcontact hFb
    ⟨C,hC,hreg⟩
  have hδw : δ ≤ w/2 := hδle.trans (min_le_right _ _)
  have hδf' : δ ≤ δf := hδle.trans (min_le_left _ _)
  have hA : PureAdmissible p hp a ha β x Q l r δ := by
    refine ⟨hEdge.trans hL,hcontact,hδ,?_,?_⟩
    · intro e he
      exact ⟨mul_lt_mul_of_pos_left (by dsimp [l]; linarith [he.1]) hp0,
        mul_lt_mul_of_pos_left (by dsimp [r]; linarith [he.2]) hp0⟩
    · intro e he
      have hel : l ≤ e := (mul_le_mul_iff_right₀ hp0).mp he.1
      have her : e ≤ r := (mul_le_mul_iff_right₀ hp0).mp he.2
      exact hSlope e ⟨by dsimp [l] at hel; linarith,by dsimp [r] at her; linarith⟩
  let g := ((p:ℝ)*l-sourceRadialEdge μ Q)/2
  have hg : 0 < g := half_pos (sub_pos.mpr hA.edge)
  have hleft : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*l := by
    dsimp [g,sourceRadialEdge] at *
    linarith [hA.edge]
  obtain ⟨hEst,⟨d⟩,_hDensityId⟩ := pure_scalar_onePoint_common p hp a ha h hcontact hg hleft
    (le_refl ((p:ℝ)*r))
  have hF' := hF.shrink_energy hδf'
  have hTail : ∀ t : ℝ, Tendsto (fun n : ℕ => mixedCriticalTailMean n μ Q (d.center n+t)
      (Ioo ((p:ℝ)*l) ((p:ℝ)*r))) atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    intro t
    apply (d.critical_tail t).congr'
    exact Eventually.of_forall (fun n => (pureCriticalTailMean_eq_scalar_tail n p hp a ha
      h.overlap_range.1 l r (d.center n+t)).symm)
  have hSimData := hSim
  obtain ⟨c,A,hc,hApos,Ω,hΩm,hΩp,hΩ⟩ := hSimData
  have hHigh : AllHighOn μ β x Q ((L₀-sourceRadialEdge μ Q)/4) C ((p:ℝ)*l) ((p:ℝ)*r) δ := by
    refine ⟨c,A,hc,hApos,Ω,hΩm,hΩp,?_⟩
    intro n J hJ
    obtain ⟨hregJ,hthird,hcrit⟩ := hΩ n J hJ
    exact ⟨hregJ,hthird,fun u hu huc hhigh =>
      ⟨(hcrit u hu huc hhigh).1,(hcrit u hu huc hhigh).2.1,(hcrit u hu huc hhigh).2.2.1⟩⟩
  have hlog : ∀ᶠ n : ℕ in atTop,
      |d.center n-((n+2:ℕ)*E-Real.log (n+2:ℕ)/(2*(β*x)))| ≤ d.log_constant := by
    filter_upwards [eventually_ge_atTop d.cutoff] with n hn
    exact (d.normalization n hn).2.2
  have hmax := maximum_limsup_of_allcritical_tail_and_localization μ h.overlap_range.1
    (mul_pos h.beta_pos h.weight_range.1) d.log_constant_pos.le hδ hc d.center hlog
      (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) measurableSet_Ioo Ω
        (fun n J hJ u hu huc hhigh => ((hΩ n J hJ).2.2 u hu huc hhigh).2.1)
          (Eventually.of_forall hΩp) hTail
  obtain ⟨hupper,hlower⟩ := pure_microscopic_envelopes p hp a ha h hA hEst d
  refine ⟨l,r,δ,hL,hR,hδf'.trans_lt hδfG,⟨{
    admissible := hA
    scalar := hEst
    point_measures := pure_point_measures p hp a ha h hA
    first_moments := d
    filter := hF'
    determinant_loss := pure_determinant_loss_of_filter p hp a ha h hF'
    localization := hHigh
    simultaneous_retention := hSim
    retained_limits := pure_retained_limits_of_filter p hp a ha h hδ hF' d
    critical_tail := hTail
    maximum_probability_limsup := hmax
    uniform_window_bound := fun A B hAB => sourceWindowMeans_uniformly_bounded_of_limits _ _
      (d.maximum_window A B hAB) (d.critical_window A B hAB)
    upper_tail_envelope := hupper
    lower_density_envelope := hlower
    lower_density_rate_lt_beta := by
      have H := mul_lt_of_lt_one_right h.beta_pos h.weight_range.2
      linarith
  }⟩⟩

/-- The Borel selection indicator, negative Hessian, closed collar and
positive-overlap separation, in a form common to both Gaussian posteriors. -/
def SelectionGeometryOn (μ : FiniteMixture) (β x Q κ C ε η δ : ℝ) : Prop :=
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  (∀ n : ℕ, Measurable (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) =>
    sourceSelectionMark (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G z.1 z.2)) ∧
  (∀ n : ℕ, ∀ J : Disorder (n+2) μ.maxDegree, ∀ u : Vector (n+2), sourceSelectionMark (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u ≤ (1:ℝ≥0∞)) ∧
  ∀ n : ℕ, ∀ J : Disorder (n+2) μ.maxDegree, ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 →
    sourceSelectionEvent (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u →
      NegativeDefiniteOperators.NegativeDefinite
        (intrinsicHessian (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) ∧
      (∀ v : Vector (n+2), ‖v‖^2=(n+2:ℕ) →
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) v=0 →
        Real.cos (min (Real.pi/4) (κ/(2*C))) ≤ overlap u v → v=u) ∧
      (∀ v : Vector (n+2), ‖v‖^2=(n+2:ℕ) →
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) v=0 →
        (n+2:ℕ)*(E-δ) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J v →
        v ≠ u → overlap u v < ε)

private theorem selection_geometry (μ : FiniteMixture) {β x Q κ C ε η δ : ℝ}
    (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ 1-Real.cos (min (Real.pi/4) (κ/(2*C))))
    (hδ : δ < gap μ Q (markY β Q) (markZ x Q) ε η/2) :
    SelectionGeometryOn μ β x Q κ C ε η δ := by
  refine ⟨fun _ => sourceSelectionMark_measurable _ κ C ε η _ _,
    fun _ J u => sourceSelectionMark_le_one _ κ C ε η _ _ J u,?_⟩
  intro n J u hu huc hSel
  exact ⟨sourceSelectionEvent_negative (by omega) _ hκ C ε η _ _ J u hu hSel,
    selection_exact_exclusion _ J hκ hC hη hδ u hu huc hSel⟩

def MixedOnePointOn (μ : FiniteMixture) (β x Q κ C ε η L R δ : ℝ) : Prop :=
  MixedPointMeasuresOn μ Q L R ∧
  Admissible μ β x Q L R δ ∧ AllHighOn μ β x Q κ C L R δ ∧
  MixedFilterOn μ β x Q κ C ε η L R δ ∧
  MixedRetainedRatioOn μ β x Q κ C ε η L R δ ∧
  SourceMarkedRadialConclusions μ β x Q L R δ ∧
  (∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ SimultaneousRetentionOn μ β x Q κ C ε η L R δ') ∧
  ∃ d : SourceMaximumAllConclusions μ β x Q L R δ,
    MixedRetainedLimitsOn μ β x Q κ C ε η L R δ d.first_moments ∧
    ∀ t : ℝ, Tendsto (fun n : ℕ => mixedCriticalTailMean n μ Q
      (d.first_moments.center n+t) (Ioo L R)) atTop (𝓝 (Real.exp (-(β*x)*t)))

/-- The analytic branches of the literal interface. A pure branch identifies
the actual finite mixture and its radial interval, so the graph counts and
posteriors refer to the same original tensor field. -/
def OnePointOn (μ : FiniteMixture) (β x Q κ C ε η L R δ : ℝ) : Prop :=
  MixedOnePointOn μ β x Q κ C ε η L R δ ∨
    ∃ (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a), μ=FiniteMixture.pure p hp a ha ∧
      ∃ l r : ℝ, L=(p:ℝ)*l ∧ R=(p:ℝ)*r ∧
        Nonempty (PureOnePointConclusions p hp a ha β x Q κ C ε η l r δ)

private theorem pure_representation_of_not_nonpure (μ : FiniteMixture)
    (hnp : ¬ μ.minDegree < μ.maxDegree) :
    ∃ (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c),
      μ = FiniteMixture.pure p hp c hc := by
  have hmin : μ.minDegree ∈ μ.coeff.support := Finset.min'_mem _ _
  have hbounds := μ.degree_bounds hmin
  have hdeg : μ.minDegree = μ.maxDegree := by omega
  let p := μ.minDegree
  have hp : 2 ≤ p := μ.minDegree_ge_two
  have hc : 0 < μ.coeff p := μ.coeff_pos hmin
  have hcoeff : μ.coeff = Finsupp.single p (μ.coeff p) := by
    ext q
    by_cases hq : q = p
    · subst q
      simp
    · have hzero : μ.coeff q = 0 := by
        by_contra hne
        have hh := μ.degree_bounds (Finsupp.mem_support_iff.mpr hne)
        dsimp only [p] at hq
        omega
      simp [hq,hzero]
  refine ⟨p,hp,μ.coeff p,hc,?_⟩
  have hinj : Function.Injective FiniteMixture.coeff := by
    intro ν₁ ν₂ heq
    cases ν₁
    cases ν₂
    cases heq
    rfl
  apply hinj
  exact hcoeff

/-- `cor:mo-interface` for every certified finite mixture, pure or non-pure
and of either parity. One pre-dimension choice supports the literal
localization/filter geometry, exact normalization, both species of ordinary
count limits, retained count limits and the sharp global-maximum tail. -/
theorem finiteMixture_onePoint_interface (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hEdge : sourceRadialEdge μ Q < L₀)
    (hm : markK μ β Q ∈ Ioo L₀ R₀) :
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧ 0 < δ ∧
          δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          SelectionGeometryOn μ β x Q κ C ε η δ ∧
          OnePointOn μ β x Q κ C ε η L R δ := by
  by_cases hnp : μ.minDegree < μ.maxDegree
  · obtain ⟨C,hκ,hC,hη,hηone,hCommon⟩ := mixed_onePoint_interface μ h hnp hEdge hm
    refine ⟨C,hκ,hC,hη,hηone,?_⟩
    intro ε hε hεη
    obtain ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,hRatio,hRad,hSim,d,hRet,hTail⟩ := hCommon ε hε hεη
    have hG : 0 < gap μ Q (markY β Q) (markZ x Q) ε
        (1-Real.cos (min (Real.pi/4) (((L₀-sourceRadialEdge μ Q)/4)/(2*C)))) := by
      linarith [hA.width]
    exact ⟨L,R,δ,hL,hR,hA.width,hδG,selection_geometry μ hκ hC le_rfl (by linarith),
      Or.inl ⟨mixed_point_measures μ h hnp hA,hA,hHigh,hF,hRatio,hRad,hSim,d,hRet,hTail⟩⟩
  · obtain ⟨p,hp,a,ha,hμ⟩ := pure_representation_of_not_nonpure μ hnp
    subst μ
    obtain ⟨C,hκ,hC,hη,hηone,hCommon⟩ := pure_onePoint_interface p hp a ha h hEdge hm
    refine ⟨C,hκ,hC,hη,hηone,?_⟩
    intro ε hε hεη
    obtain ⟨l,r,δ,hL,hR,hδG,⟨d⟩⟩ := hCommon ε hε hεη
    have hG : 0 < gap (FiniteMixture.pure p hp a ha) Q (markY β Q) (markZ x Q) ε
        (1-Real.cos (min (Real.pi/4)
          (((L₀-sourceRadialEdge (FiniteMixture.pure p hp a ha) Q)/4)/(2*C)))) := by
      linarith [d.admissible.width]
    exact ⟨(p:ℝ)*l,(p:ℝ)*r,δ,hL,hR,d.admissible.width,hδG,
      selection_geometry _ hκ hC le_rfl (by linarith),
      Or.inr ⟨p,hp,a,ha,rfl,l,r,rfl,rfl,⟨d⟩⟩⟩

end SlowEquilibration.SourceMixedOnePointInterface
