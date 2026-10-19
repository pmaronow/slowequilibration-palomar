-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedFullWindowMoments

/-! Source 11.13 first-moment normalization for the literal selected
proper-pure count, with the same fixed selection constants as its
second-moment bound. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalMarkedWindows
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open LatitudeGroundTrial
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_pure_actual_retained_center_first_moment
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ n₀ : ℕ, ∃ m : ℕ → ℝ, ∃ M C cut η ε δ C₂ D : ℝ,
      0 < M ∧ 0 < δ ∧ 0 < C ∧ 0 < cut ∧ 0 < η ∧ 0 < ε ∧ 0 < C₂ ∧ 0 < D ∧
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      (∀ n < n₀, m n=(n+2 : ℕ)*E) ∧
      (∀ n ≥ n₀, tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
        (∀ y : ℝ, tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R))
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourceRetainedValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R)
          (g/2) C ε η E G)
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ᶠ n : ℕ in atTop, ∀ I : Set ℝ,
        MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
          let aN := sourceRetainedValueWindowMean (n+2) μ Q I
            (g/2) C ε η E G
          let bN := sourceUnfilteredValueWindowMean (n+2) μ Q I
          let X := fun J => (sourceRetainedValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q) I
            (g/2) C ε η E G J).toReal
          aN ≤ bN ∧
          (∫ J, X J ∂disorderLaw (n+3) μ.maxDegree) = aN ∧
          MemLp X 2 (disorderLaw (n+3) μ.maxDegree) ∧
          sourceRetainedValueWindowSecondMoment (n+2) μ Q I
            (g/2) C ε η E G ≤
            (1+D*sourcePrintedPairError (3/8 : ℝ) n)*aN^2+
              (1+(1-ε)/(cut^2-ε))*aN ∧
          ProbabilityTheory.variance X (disorderLaw (n+3) μ.maxDegree) ≤
            D*sourcePrintedPairError (3/8 : ℝ) n*aN^2+
              (1+(1-ε)/(cut^2-ε))*aN) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let δMax := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(4*(p : ℝ))
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hδMax : 0 < δMax := div_pos hedge (by positivity)
  obtain ⟨C,cut,η,ε,δ,C₂,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
      hε,hεCut,hεη,hδ,hδG,hδBound,hC₂,grid,hgrid,hError,hFull⟩ :=
    source_pure_actual_retained_fixed_window_full_moments p hp a ha h hδMax
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hm : E ∈ Ioo (E-δ) (E+δ) := by constructor <;> dsimp [E] <;> linarith
  have hLeft : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p : ℝ)*(E-δ) :=
    source_pure_value_box_edge_margin p hp a ha h hδBound (E-δ)
      (by constructor <;> linarith)
  obtain ⟨n₀,m,M,hM,hFallback,hCenter,hCritical⟩ :=
    sourcePure_truncatedCritical_center_count_limits p hp a ha h hm hg hLeft le_rfl
  obtain ⟨D,hD,hMoments⟩ := hFull (by norm_num : (1/4 : ℝ) < 3/8)
    (by norm_num : (3/8 : ℝ) < 1/2)
  have hUnfiltered : ∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
      sourceUnfilteredValueWindowMean (n+2) μ Q
        (sourcePureCenteredNormalizedWindow n m E δ L R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))) := by
    intro L R hLR
    have ht := (hCritical L R hLR).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ =>
      sourcePureTruncatedCriticalWindowMean (n+1) p hp a ha Q
        (E-δ) (E+δ) (m (n+1)+L) (m (n+1)+R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))) at ht
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun n =>
      (sourcePureCenteredNormalizedWindow_critical_mean n p hp a ha
        Q E δ L R m).symm)
  refine ⟨n₀,m,M,C,cut,η,ε,δ,C₂,D,hM,hδ,hC,hcut,hη,hε,hC₂,hD,
    hFallback,hCenter,hUnfiltered,?_,?_⟩
  · intro L R hLR
    let bN := fun n : ℕ => sourceUnfilteredValueWindowMean (n+2) μ Q
      (sourcePureCenteredNormalizedWindow n m E δ L R)
    let aN := fun n : ℕ => sourceRetainedValueWindowMean (n+2) μ Q
      (sourcePureCenteredNormalizedWindow n m E δ L R) (g/2) C ε η E G
    let eN := fun n : ℕ => sourceSelectionWeightError C₂ μ Q G g grid (n+1)
    have hb : Tendsto bN atTop
        (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))) := by
      exact hUnfiltered L R hLR
    have he : Tendsto eN atTop (𝓝 (0 : ℝ)) :=
      hError.comp (tendsto_add_atTop_nat 1)
    have hfactor : Tendsto (fun n => 1-eN n) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub he)
    have hlower : Tendsto (fun n => (1-eN n)*bN n) atTop
        (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))) := by
      simpa only [one_mul] using hfactor.mul hb
    have hBounds : ∀ᶠ n : ℕ in atTop,
        (1-eN n)*bN n ≤ aN n ∧ aN n ≤ bN n := by
      filter_upwards [hMoments] with n hn
      have hi := hn (sourcePureCenteredNormalizedWindow n m E δ L R)
        (sourcePureCenteredNormalizedWindow_measurable n m E δ L R)
        (sourcePureCenteredNormalizedWindow_subset_value_box n m E δ L R)
      exact ⟨hi.1,hi.2.1⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hb
      (hBounds.mono fun _ hn => hn.1) (hBounds.mono fun _ hn => hn.2)
  · filter_upwards [hMoments] with n hn
    intro I hI hsub
    exact ⟨(hn I hI hsub).2.1,(hn I hI hsub).2.2.1,
      (hn I hI hsub).2.2.2.1,(hn I hI hsub).2.2.2.2.1,
      (hn I hI hsub).2.2.2.2.2⟩

end SlowEquilibration.PairConditionalDeterminantMoments
