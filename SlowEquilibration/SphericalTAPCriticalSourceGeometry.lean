-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalFixedBandPalmLower
public import SlowEquilibration.SourcePhysicalPurePairSelectionFailureProbability

@[expose] public section

/-! The geometric and mark-compatibility part of the neighborhood choice
preceding source Proposition 12.20. The analytic Hessian and regression
inequalities of the printed choice remain separate obligations. -/

namespace SlowEquilibration.SphericalTAPCriticalSourceGeometry
noncomputable section
open Set SphericalTAPCertificate SphericalMarkedWindows TwoAtomStationarity
set_option autoImplicit false

/-- A source certificate supplies one common radial interval, compact mark
bound, latitude cap, and positive energy width for every smaller fixed band. -/
theorem mixed_fixedBand_source_geometry
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ M r L R ε0 b0 : ℝ,
      0 ≤ M ∧ 0 ≤ r ∧ r < 1 ∧ 0 < ε0 ∧
      0 < b0 ∧ b0 < Real.sqrt Q ∧
      edge < L ∧ L < K ∧ K < R ∧
      Icc L R ⊆ Icc (-M) M ∧ |E|+ε0 ≤ M ∧
      ∀ b : ℝ, 0 < b → b ≤ b0 →
        Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Icc (-r) r := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  have hgap : edge < K := by
    have hh : 0 < markK μ β Q - 2*Real.sqrt (Q^2*μ.xi2 Q) := by
      simpa only [markB] using h.edge_margin.2.2
    change 2*Real.sqrt (Q^2*μ.xi2 Q) < markK μ β Q
    linarith
  have hQ0 : 0 < Real.sqrt Q := Real.sqrt_pos.2 h.overlap_range.1
  have hQ1 : Real.sqrt Q < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  let L := (edge+K)/2
  let R := K+(K-edge)/2
  let r := (1+Real.sqrt Q)/2
  let b0 := min (Real.sqrt Q/2) ((1-Real.sqrt Q)/2)
  let ε0 : ℝ := 1
  let M := max |E| (max |L| |R|)+2
  refine ⟨M,r,L,R,ε0,b0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [M]; positivity
  · dsimp [r]; positivity
  · dsimp [r]; linarith
  · norm_num [ε0]
  · dsimp [b0]; exact lt_min (by positivity) (by linarith)
  · dsimp [b0]; linarith [min_le_left (Real.sqrt Q/2) ((1-Real.sqrt Q)/2)]
  · dsimp [L]; linarith
  · dsimp [L]; linarith
  · dsimp [R]; linarith
  · intro y hy
    dsimp [M]
    constructor
    · have hL : -|L| ≤ L := neg_abs_le L
      have hM : |L| ≤ max |L| |R| := le_max_left _ _
      have hM' : max |L| |R| ≤ max |E| (max |L| |R|) := le_max_right _ _
      linarith [hy.1]
    · have hR : R ≤ |R| := le_abs_self R
      have hM : |R| ≤ max |L| |R| := le_max_right _ _
      have hM' : max |L| |R| ≤ max |E| (max |L| |R|) := le_max_right _ _
      linarith [hy.2]
  · dsimp [M,ε0]
    linarith [le_max_left |E| (max |L| |R|)]
  · intro b hb hb0 y hy
    have hbl : b ≤ Real.sqrt Q/2 := hb0.trans (min_le_left _ _)
    have hbr : b ≤ (1-Real.sqrt Q)/2 := hb0.trans (min_le_right _ _)
    dsimp [r]
    constructor
    · linarith [hy.1]
    · linarith [hy.2]

/-- In a proper-pure model the deterministic Euler radial mark stays strictly
above the GOE edge throughout a source-sized energy window. -/
theorem pure_fixedBand_radial_window
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ ε0 g Z : ℝ, 0 < ε0 ∧ 0 < g ∧
      ∀ a : ℝ, |a-E| ≤ ε0 → edge+g ≤ (p:ℝ)*a ∧ (p:ℝ)*a ≤ Z := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let K := markK μ β Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  have hgap : edge < K := by
    have hh : 0 < markK μ β Q - 2*Real.sqrt (Q^2*μ.xi2 Q) := by
      simpa only [markB] using h.edge_margin.2.2
    change 2*Real.sqrt (Q^2*μ.xi2 Q) < markK μ β Q
    linarith
  have hEuler : K=(p:ℝ)*E :=
    PairConditionalDeterminantMoments.source_pure_markK_eq_degree_mul_markE
      p hp alpha halpha h
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  let g := (K-edge)/2
  let ε0 := g/(2*(p:ℝ))
  let Z := K+g
  refine ⟨ε0,g,Z,?_,?_,?_⟩
  · dsimp [ε0,g]; positivity
  · dsimp [g]; linarith
  · intro a ha
    have halo : E-ε0 ≤ a := by linarith [(abs_le.mp ha).1]
    have hahi : a ≤ E+ε0 := by linarith [(abs_le.mp ha).2]
    have hpε : (p:ℝ)*ε0 = g/2 := by
      dsimp [ε0]
      field_simp
    have hgRel : 2*g=K-edge := by dsimp [g]; ring
    have hLower := mul_le_mul_of_nonneg_left halo hp0.le
    have hUpper := mul_le_mul_of_nonneg_left hahi hp0.le
    constructor <;> nlinarith [hEuler,hgRel,hLower,hUpper]

end
end SlowEquilibration.SphericalTAPCriticalSourceGeometry
