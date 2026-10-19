-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalSourceGeometry
public import SlowEquilibration.SourcePhysicalPairRetainedWindowGeometry
public import SlowEquilibration.SphericalOnePointRadialCurvature

@[expose] public section

/-! Concrete portions of the simultaneous neighborhood choice in manuscript
Section 12: the quadratic latitude bank and the energy score. The joint
mixed `(k,a)` Hessian and pure latitude Hessian remain separate inputs. -/

namespace SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open PairConditionalDeterminantMoments
open scoped Topology
set_option autoImplicit false

/-- The exact quadratic-bank variance `v₂(a)` printed in Lemma 12.8. -/
def sourceQuadraticLatitudeVariance (μ : FiniteMixture) (a : ℝ) : ℝ :=
  (1-a^2)^2*μ.xi2 (a^2)/2

theorem sourceQuadraticLatitudeVariance_continuous (μ : FiniteMixture) :
    Continuous (sourceQuadraticLatitudeVariance μ) := by
  unfold sourceQuadraticLatitudeVariance
  have hxi : Continuous μ.xi2 := by
    unfold FiniteMixture.xi2
    fun_prop
  fun_prop

/-- At the contact latitude, the bank second-moment parameter is precisely
the certificate edge ratio `b_Q/y²`, without an independent stability axiom. -/
theorem quadratic_contact_eq_edge_ratio (μ : FiniteMixture)
    {β Q : ℝ} (hβ : 0 < β) (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    2*β^2*sourceQuadraticLatitudeVariance μ (Real.sqrt Q) =
      markB μ Q/(markY β Q)^2 := by
  have hQ0 : Q ≠ 0 := hQ.1.ne'
  have hβ0 : β ≠ 0 := hβ.ne'
  have hs : 1-Q ≠ 0 := ne_of_gt (sub_pos.mpr hQ.2)
  rw [sourceQuadraticLatitudeVariance, Real.sq_sqrt hQ.1.le]
  unfold markB markY
  field_simp

/-- A source certificate makes the actual quadratic bank subcritical at the
contact latitude. -/
theorem quadratic_contact_strict (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    2*β^2*sourceQuadraticLatitudeVariance μ (Real.sqrt Q) < 1 := by
  rw [quadratic_contact_eq_edge_ratio μ h.beta_pos h.overlap_range]
  exact h.edge_margin.1

/-- The strict contact inequality persists on a closed physical latitude
band, with an explicit positive margin `ε₂<1`. -/
theorem quadratic_fixed_band_margin (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    ∃ b0 ε2 : ℝ, 0 < b0 ∧ b0 < Real.sqrt Q ∧
      0 < ε2 ∧ ε2 < 1 ∧
      Icc (Real.sqrt Q-b0) (Real.sqrt Q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ b : ℝ, 0 < b → b ≤ b0 →
        ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
          2*β^2*sourceQuadraticLatitudeVariance μ a ≤ 1-ε2 := by
  let q : ℝ := Real.sqrt Q
  let f : ℝ → ℝ := fun a => 2*β^2*sourceQuadraticLatitudeVariance μ a
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hf : f q < 1 := quadratic_contact_strict μ h
  let ε2 := (1-f q)/2
  have hε2 : 0 < ε2 := by dsimp [ε2]; linarith
  have hbank : ∀ᶠ a : ℝ in 𝓝 q, f a < 1-ε2 := by
    have hc : ContinuousAt f q := by
      dsimp [f]
      exact (continuous_const.mul
        (sourceQuadraticLatitudeVariance_continuous μ)).continuousAt
    exact hc.tendsto.eventually (gt_mem_nhds (by dsimp [ε2]; linarith))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hbank
  let b0 := min (min (q/2) ((1-q)/2)) (r/2)
  have hb0 : 0 < b0 := by dsimp [b0]; positivity
  have hbr : b0 < r := by dsimp [b0]; linarith [min_le_right (min (q/2) ((1-q)/2)) (r/2)]
  have hbq : b0 < q := by
    have h1 := min_le_left (min (q/2) ((1-q)/2)) (r/2)
    have h2 := min_le_left (q/2) ((1-q)/2)
    dsimp [b0]
    linarith
  have hb1 : b0 < 1-q := by
    have h1 := min_le_left (min (q/2) ((1-q)/2)) (r/2)
    have h2 := min_le_right (q/2) ((1-q)/2)
    dsimp [b0]
    linarith
  refine ⟨b0,ε2,hb0,hbq,hε2,?_,?_,?_⟩
  · have hfv : 0 ≤ f q := by
      dsimp [f,sourceQuadraticLatitudeVariance]
      have hxi : 0 ≤ μ.xi2 Q := (μ.xi2_pos h.overlap_range.1).le
      rw [Real.sq_sqrt h.overlap_range.1.le]
      positivity
    dsimp [ε2]
    linarith
  · intro a ha
    constructor <;> dsimp [q] at * <;> linarith [ha.1,ha.2]
  · intro b hb hbb a ha
    have hdist : dist a q < r := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt (abs_le.mpr ?_) hbr
      constructor <;> linarith [ha.1,ha.2,hbb]
    exact (hball hdist).le

/-- One mixed-model selection simultaneously retains a compact interval
above the GOE edge, the source microscopic energy-score bounds, radial
strict concavity of the literal marked complexity, and the quadratic-bank
margin on every smaller fixed latitude band. This is the part of the printed
Section 12 choice that does not require the joint `(k,a)` Hessian. -/
theorem mixed_source_slope_radial_and_quadratic_choice
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ L R ε0 b0 ε2 cstar : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ b0 < Real.sqrt Q ∧
      0 < ε2 ∧ ε2 < 1 ∧ 0 < cstar ∧
      edge < L ∧ L < K ∧ K < R ∧
      Icc (Real.sqrt Q-b0) (Real.sqrt Q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      (∀ b : ℝ, 0 < b → b ≤ b0 →
        ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
          2*β^2*sourceQuadraticLatitudeVariance μ a ≤ 1-ε2) ∧
      ∀ e ∈ Icc (E-ε0) (E+ε0), ∀ k ∈ Icc L R,
        (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧
        sourceEnergySlope μ Q e k ≤ (β*x+β)/2 ∧
        deriv (sourceRadialProfileDerivative μ Q e) k ≤ -cstar := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  obtain ⟨M,r,Lg,Rg,εg,bg,_,_,_,hεg,hbg,hbgQ,hEdge,hLgK,hKRg,
    _,_,_⟩ := SphericalTAPCriticalSourceGeometry.mixed_fixedBand_source_geometry μ h
  obtain ⟨ρ,hρ,hscore⟩ := source_contact_score_neighborhood μ h hnp
  obtain ⟨bq,ε2,hbq,hbqQ,hε2,hε2one,hI,hbank⟩ :=
    quadratic_fixed_band_margin μ h
  let L := max Lg (K-ρ/2)
  let R := min Rg (K+ρ/2)
  let ε0 := min εg ρ
  let b0 := min bg bq
  let cstar := sourceRadialCurvature μ Q
  have hε0 : 0 < ε0 := lt_min hεg hρ
  have hb0 : 0 < b0 := lt_min hbg hbq
  have hLc : L < K := max_lt hLgK (by dsimp [K]; linarith)
  have hRc : K < R := lt_min hKRg (by dsimp [K]; linarith)
  have hEdgeL : 2*Real.sqrt (Q^2*μ.xi2 Q) < L :=
    hEdge.trans_le (le_max_left _ _)
  have hcurv : 0 < cstar := sourceRadialCurvature_pos μ h.overlap_range.1 hnp
  refine ⟨L,R,ε0,b0,ε2,cstar,hε0,hb0,?_,hε2,hε2one,hcurv,
    hEdgeL,hLc,hRc,?_,?_,?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) hbqQ
  · intro a ha
    apply hI
    constructor
    · have hh := min_le_right bg bq
      dsimp [b0] at *
      linarith [ha.1]
    · have hh := min_le_right bg bq
      dsimp [b0] at *
      linarith [ha.2]
  · intro b hb hbb a ha
    apply hbank b hb (hbb.trans (min_le_right _ _)) a ha
  · intro e he k hk
    have heρ : |e-E| ≤ ρ := by
      apply abs_le.mpr
      have hmin := min_le_right εg ρ
      constructor <;> dsimp [ε0] at * <;> linarith [he.1,he.2]
    have hkρ : |k-K| ≤ ρ := by
      apply abs_le.mpr
      have hll := le_max_right Lg (K-ρ/2)
      have hrr := min_le_right Rg (K+ρ/2)
      constructor <;> dsimp [L,R] at * <;> linarith [hk.1,hk.2]
    obtain ⟨hslo,hshi⟩ := hscore e k heρ hkρ
    refine ⟨hslo,hshi,?_⟩
    exact sourceRadialProfile_second_derivative_le μ h.overlap_range.1 e k
      (hEdgeL.trans_le hk.1)

end
end SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood
