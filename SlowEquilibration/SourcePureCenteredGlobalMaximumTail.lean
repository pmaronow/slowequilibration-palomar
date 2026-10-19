-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCenteredCriticalNearTail
public import Mathlib.Topology.Order.LiminfLimsup

/-! Global-maximum upper tail for the original proper-pure field at any
source logarithmic center. The compact energy cutoff is explicit. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem sourcePure_centered_global_maximum_limsup_with_cutoff
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let δ := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(8*(p : ℝ))
    let s := E+δ/2
    let K := ∑ q : Degree μ.maxDegree,
      2 * Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
        Real.sqrt q.val.val
    ∃ A : ℝ, 0 < A ∧ ∀ L B : ℝ, max s 0 < B →
      Filter.limsup (fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
        {J | m n+L ≤ sourceSphereMaximum n μ Q J}) atTop ≤
        A*Real.exp (-(β*x)*L)+K/B := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let δ := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(8*(p : ℝ))
  let s := E+δ/2
  let K := ∑ q : Degree μ.maxDegree,
    2 * Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
      Real.sqrt q.val.val
  obtain ⟨hδ,A,hA,hNear⟩ :=
    sourcePure_centered_near_critical_mean_upper p hp a ha h m hM hcenter
  refine ⟨A,hA,?_⟩
  intro L B hB
  have hsE : E < s := by dsimp [s]; linarith
  have hsB : s ≤ B := (le_max_left _ _).trans hB.le
  have hBpos : 0 < B := (le_max_right _ _).trans_lt hB
  have hHigh := sourcePure_high_strip_critical_mean_tendsto_zero
    p hp a ha h hsE hsB
  have hNear := hNear L
  let P : ℕ → ℝ := fun n => (disorderLaw (n+2) μ.maxDegree).real
    {J | m n+L ≤ sourceSphereMaximum n μ Q J}
  let Z : ℕ → ℝ := fun n => sourceUnfilteredValueWindowMean (n+1) μ Q (Icc s B)
  have hProb : ∀ᶠ n : ℕ in atTop,
      P n ≤ A*Real.exp (-(β*x)*L)+Z n+K/B := by
    filter_upwards [hNear] with n hn
    let H := m n+L
    let S := (n+2 : ℕ)*s
    let T := (n+2 : ℕ)*B
    let f := sourceSphereMaximum n μ Q
    let Pn := disorderLaw (n+2) μ.maxDegree
    have hsub : {J : Disorder (n+2) μ.maxDegree | H ≤ f J} ⊆
        ({J | H ≤ f J ∧ f J ≤ S} ∪ {J | S ≤ f J ∧ f J ≤ T}) ∪
          {J | T ≤ f J} := by
      intro J hJ
      by_cases hS : f J ≤ S
      · exact Or.inl (Or.inl ⟨hJ,hS⟩)
      by_cases hT : f J ≤ T
      · exact Or.inl (Or.inr ⟨le_of_lt (lt_of_not_ge hS),hT⟩)
      · exact Or.inr (le_of_lt (lt_of_not_ge hT))
    have hUnion : P n ≤
        Pn.real {J | H ≤ f J ∧ f J ≤ S}+
          Pn.real {J | S ≤ f J ∧ f J ≤ T}+
            Pn.real {J | T ≤ f J} := by
      apply (measureReal_mono hsub (measure_ne_top _ _)).trans
      exact (measureReal_union_le _ _).trans
        (by simpa only [add_assoc] using
          add_le_add (measureReal_union_le _ _) le_rfl)
    have hNearProb := sourceSphereMaximum_between_probability_le_critical_mean
      n μ h.overlap_range.1 H S
    have hHighProb := sourceSphereMaximum_between_probability_le_critical_mean
      n μ h.overlap_range.1 S T
    have hFarProb := sourceSphereMaximum_coarse_upper_tail n μ Q hBpos
    have hS : S/(n+2 : ℕ)=s := by dsimp [S]; field_simp
    have hT : T/(n+2 : ℕ)=B := by dsimp [T]; field_simp
    rw [hS] at hNearProb hHighProb
    rw [hT] at hHighProb
    have hNearBound : Pn.real {J | H ≤ f J ∧ f J ≤ S} ≤
        A*Real.exp (-(β*x)*L) := hNearProb.trans hn
    have hHighBound : Pn.real {J | S ≤ f J ∧ f J ≤ T} ≤ Z n := hHighProb
    have hFarBound : Pn.real {J | T ≤ f J} ≤ K/B := hFarProb
    exact hUnion.trans (add_le_add (add_le_add hNearBound hHighBound) hFarBound)
  have hUpper : Tendsto (fun n : ℕ => A*Real.exp (-(β*x)*L)+Z n+K/B)
      atTop (𝓝 (A*Real.exp (-(β*x)*L)+K/B)) := by
    simpa only [Z,add_zero] using
      ((tendsto_const_nhds.add hHigh).add tendsto_const_nhds :
        Tendsto (fun n : ℕ => A*Real.exp (-(β*x)*L)+Z n+K/B)
          atTop (𝓝 ((A*Real.exp (-(β*x)*L)+0)+K/B)))
  have hLow : IsCoboundedUnder (· ≤ ·) atTop P :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  exact (limsup_le_limsup hProb hLow hUpper.isBoundedUnder_le).trans_eq hUpper.limsup_eq

/-- The compact cutoff can be sent to infinity: the literal pure global
maximum has an exponentially decaying centered probability upper tail. -/
theorem sourcePure_centered_global_maximum_limsup
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ,
      Filter.limsup (fun n : ℕ =>
        (disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree).real
          {J | m n+L ≤ sourceSphereMaximum n (FiniteMixture.pure p hp a ha) Q J})
        atTop ≤ A*Real.exp (-(β*x)*L) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let δ := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(8*(p : ℝ))
  let s := E+δ/2
  let K := ∑ q : Degree μ.maxDegree,
    2 * Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
      Real.sqrt q.val.val
  obtain ⟨A,hA,hcut⟩ := sourcePure_centered_global_maximum_limsup_with_cutoff
    p hp a ha h m hM hcenter
  refine ⟨A,hA,?_⟩
  intro L
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => by positivity)
  apply le_of_forall_pos_le_add
  intro ε hε
  let B := max s 0+K/ε+1
  have hB : max s 0 < B := by
    have hkdiv : 0 ≤ K/ε := div_nonneg hK hε.le
    dsimp [B]
    linarith
  have hKε : K/B ≤ ε := by
    apply (div_le_iff₀ ((le_max_right s 0).trans_lt hB)).mpr
    have hmax : 0 ≤ max s 0 := le_max_right s 0
    dsimp [B]
    have hEq : ε*(K/ε)=K := by field_simp
    nlinarith [mul_nonneg hε.le hmax]
  have hh := hcut L B hB
  exact hh.trans (by linarith)

end SlowEquilibration.SphericalMarkedWindows
