-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureGuerra

/-! Compactly uniform actual linear spherical endpoints for arbitrary
continuous nonnegative trial-variance and Dirac-atom families. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def linearEntropy (β d t : ℝ) : ℝ := (β^2*d*(1-t)+t/(1-t)+Real.log (1-t))/2

theorem linearEntropy_eq_trial (β d : ℝ) {t : ℝ} (ht : t<1) :
    linearEntropy β d t=SphericalModel.quenchedLinearTrial (β^2*d) ((1-t)⁻¹) := by
  unfold linearEntropy SphericalModel.quenchedLinearTrial
  rw [Real.log_inv]
  have hne : 1-t≠0 := ne_of_gt (sub_pos.mpr ht)
  field_simp [hne]
  ring

theorem linearEntropy_continuous {Z : Type*} [TopologicalSpace Z] (β : ℝ)
    (d t : Z → ℝ) (hd : Continuous d) (ht : Continuous t) (ht1 : ∀z,t z<1) :
    Continuous (fun z => linearEntropy β (d z) (t z)) := by
  have hs : Continuous (fun z => 1-t z) := continuous_const.sub ht
  have hne (z : Z) : 1-t z≠0 := ne_of_gt (sub_pos.mpr (ht1 z))
  unfold linearEntropy
  exact (((((hd.const_mul (β^2)).mul hs).add (ht.div hs hne)).add (hs.log hne)).div_const 2)

/-- The genuine Gaussian-shell endpoint is uniform on compact scalar
families. Its dimension threshold uses only d,t and the requested error. -/
theorem eventually_uniform_linear_Dirac_upper {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (β : ℝ) (d t : Z → ℝ) (hd : Continuous d) (ht : Continuous t)
    (hd0 : ∀z,0≤d z) (htR : ∀z,t z∈Ico (0:ℝ) 1) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀z : Z,
      (n:ℝ)/((n+1:ℕ):ℝ)*SphericalModel.linearSphereQuenchedPressure n (trialVariance n β (d z))≤
        linearEntropy β (d z) (t z)+ε := by
  classical
  let δ := ε/4
  have hδ : 0<δ := by dsimp [δ];positivity
  let kInf := fun z : Z => β^2*d z
  let k := fun c : Z => kInf c+δ
  let s := fun c : Z => (1-t c)⁻¹
  have hkInf : Continuous kInf := hd.const_mul (β^2)
  have hkInf0 (z : Z) : 0≤kInf z := mul_nonneg (sq_nonneg β) (hd0 z)
  have hk0 (c : Z) : 0≤k c := add_nonneg (hkInf0 c) hδ.le
  have hs0 (c : Z) : 0<s c := inv_pos.mpr (sub_pos.mpr (htR c).2)
  have hs1 (c : Z) : 1 ≤ s c := by
    change 1≤(1-t c)⁻¹
    rw [inv_eq_one_div]
    apply (one_le_div (sub_pos.mpr (htR c).2)).mpr
    linarith [(htR c).1]
  have hEnt := linearEntropy_continuous β d t hd ht (fun z => (htR z).2)
  let U := fun c : Z => {z : Z | kInf z<k c-δ/2 ∧
    SphericalModel.quenchedLinearTrial (k c) (s c)<linearEntropy β (d z) (t z)+ε/2}
  have hU (c : Z) : IsOpen (U c) :=
    (isOpen_lt hkInf continuous_const).inter (isOpen_lt continuous_const (hEnt.add continuous_const))
  have hCenter (c : Z) : c∈U c := by
    have heq : SphericalModel.quenchedLinearTrial (k c) (s c)=linearEntropy β (d c) (t c)+δ/(2*s c) := by
      rw [linearEntropy_eq_trial β (d c) (htR c).2]
      dsimp [k,kInf,s]
      unfold SphericalModel.quenchedLinearTrial
      ring
    have hSmall : δ/(2*s c)≤δ/2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (hs0 c))).mpr
      have hm := mul_le_mul_of_nonneg_left (hs1 c) (by positivity : 0≤δ/2)
      nlinarith
    constructor
    · dsimp [k]
      linarith
    · rw [heq]
      dsimp [δ] at hSmall
      linarith
  obtain ⟨T,hcover⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro z _
    exact mem_iUnion.mpr ⟨z,hCenter z⟩)
  have hEvent : ∀c∈T,∀ᶠ n : ℕ in atTop,
      SphericalModel.linearSphereQuenchedPressure n (k c)≤SphericalModel.quenchedLinearTrial (k c) (s c)+ε/4 ∧
      k c/(n:ℝ)<δ/2 := by
    intro c _
    have hl := SphericalModel.linearSphereQuenchedPressure_eventually_upper (hk0 c) (hs1 c)
      (by positivity : 0<ε/4)
    have hh := (tendsto_const_div_atTop_nhds_zero_nat (k c)).eventually
      (gt_mem_nhds (half_pos hδ))
    exact hl.and hh
  filter_upwards [T.eventually_all.mpr hEvent,eventually_ge_atTop 1] with n hEvent hn
  intro z
  obtain ⟨c,hcT,hcz⟩ := mem_iUnion₂.mp (hcover (mem_univ z))
  have hκ : 0≤trialVariance n β (d z) := trialVariance_nonneg n β (hd0 z)
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hkBound : kInf z≤k c := by linarith [hcz.1]
  have hEq : trialVariance n β (d z)=kInf z+kInf z/(n:ℝ) := by
    dsimp [kInf]
    unfold trialVariance
    field_simp [hnpos.ne']
    push_cast
    ring
  have hκBound : trialVariance n β (d z)≤k c := by
    rw [hEq]
    have hDiv := div_le_div_of_nonneg_right hkBound hnpos.le
    linarith [hcz.1,(hEvent c hcT).2]
  have hLin := (SphericalModel.linearSphereQuenchedPressure_mono hn hκ hκBound).trans (hEvent c hcT).1
  have hα0 : 0≤(n:ℝ)/((n+1:ℕ):ℝ) := by positivity
  have hNpos : 0<((n+1:ℕ):ℝ) := by positivity
  have hα1 : (n:ℝ)/((n+1:ℕ):ℝ)≤1 := by
    apply (div_le_one hNpos).mpr
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  have hTrial : 0≤SphericalModel.quenchedLinearTrial (k c) (s c) := by
    have hlog := Real.log_le_sub_one_of_pos (hs0 c)
    have hdiv := div_nonneg (hk0 c) (hs0 c).le
    unfold SphericalModel.quenchedLinearTrial
    linarith
  have hRight0 : 0≤SphericalModel.quenchedLinearTrial (k c) (s c)+ε/4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hLin hα0
  have h2 := mul_le_mul_of_nonneg_right hα1 hRight0
  simp only [one_mul] at h2
  linarith [hcz.2]

end SlowEquilibration.GaussianFeatureDirac
