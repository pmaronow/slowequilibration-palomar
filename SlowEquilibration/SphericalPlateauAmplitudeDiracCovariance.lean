-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeScalar
public import SlowEquilibration.FiniteNonnegativePolynomialTangent

@[expose] public section

/-! # True Dirac tangent support for the perturbed latitude bank

The literal transverse covariance retains its constant and linear terms.
All coefficients are nonnegative on every physical latitude, for all real
amplitudes. A fixed original Dirac atom supplies a uniform negative cutoff.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set
open SphericalModel
open scoped Topology BigOperators
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal coefficient of each independent tensor block in the actual
latitude covariance, including transverse degrees zero and one. -/
def amplitudeLatitudeCoefficient (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r : ℝ) (i : BankIndex μ) : ℝ :=
  bankAmplitude p₀ s i^2*mixtureCoefficients μ i.1*(Nat.choose i.1.val.val i.2.val : ℝ)*
    r^(2*(i.1.val.val-i.2.val))*(1-r^2)^i.2.val

def amplitudeLatitudeCovarianceFirst (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r t : ℝ) : ℝ :=
  FiniteNonnegativePolynomial.firstDerivative (fun i : BankIndex μ => i.2.val)
    (amplitudeLatitudeCoefficient μ p₀ s r) t

theorem amplitudeLatitudeCoefficient_nonneg (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r|≤1) (i : BankIndex μ) :
    0≤amplitudeLatitudeCoefficient μ p₀ s r i := by
  have hpow : 0≤r^(2*(i.1.val.val-i.2.val)) := by rw [pow_mul];positivity
  have hsq : 0≤1-r^2 := by nlinarith [abs_le.mp hr]
  unfold amplitudeLatitudeCoefficient
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
    (mixtureCoefficients_nonnegative μ i.1)) (Nat.cast_nonneg _)) hpow) (pow_nonneg hsq _)

theorem amplitudeLatitudeCoefficient_joint_continuous (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (i : BankIndex μ) :
    Continuous (fun z : (Fin 2 → ℝ) × ℝ => amplitudeLatitudeCoefficient μ p₀ z.1 z.2 i) := by
  unfold amplitudeLatitudeCoefficient bankAmplitude
  split_ifs <;> fun_prop

theorem amplitudeLatitudeCovariance_eq_polynomial (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r : ℝ) :
    amplitudeLatitudeCovariance μ p₀ s r=
      FiniteNonnegativePolynomial.covariance (fun i : BankIndex μ => i.2.val)
        (amplitudeLatitudeCoefficient μ p₀ s r) := rfl

theorem amplitudeLatitudeCovariance_hasDerivAt (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r t : ℝ) :
    HasDerivAt (amplitudeLatitudeCovariance μ p₀ s r) (amplitudeLatitudeCovarianceFirst μ p₀ s r t) t := by
  rw [amplitudeLatitudeCovariance_eq_polynomial]
  exact FiniteNonnegativePolynomial.covariance_hasDerivAt _ _ t

theorem amplitudeLatitudeCovarianceFirst_nonneg (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r t : ℝ} (hr : |r|≤1) (ht : 0≤t) :
    0≤amplitudeLatitudeCovarianceFirst μ p₀ s r t :=
  FiniteNonnegativePolynomial.firstDerivative_nonneg _ _
    (amplitudeLatitudeCoefficient_nonneg μ p₀ s hr) ht

/-- The actual amplitude covariance is convex on nonnegative transverse
overlaps, with no parity or amplitude-nearness restriction. -/
theorem amplitudeLatitudeCovariance_convexOn_Ici (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r|≤1) :
    ConvexOn ℝ (Ici 0) (amplitudeLatitudeCovariance μ p₀ s r) := by
  rw [amplitudeLatitudeCovariance_eq_polynomial]
  exact FiniteNonnegativePolynomial.covariance_convexOn_Ici _ _
    (amplitudeLatitudeCoefficient_nonneg μ p₀ s hr)

/-- Constant and linear bank terms cause no deficit. The literal supporting
line remains valid down to minus the chosen nonnegative Dirac atom. -/
theorem amplitudeLatitudeCovariance_tangent_le (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r t z : ℝ} (hr : |r|≤1) (ht : 0≤t) (hz : -t≤z) :
    amplitudeLatitudeCovariance μ p₀ s r t+amplitudeLatitudeCovarianceFirst μ p₀ s r t*(z-t)≤
      amplitudeLatitudeCovariance μ p₀ s r z := by
  rw [amplitudeLatitudeCovariance_eq_polynomial]
  exact FiniteNonnegativePolynomial.covariance_tangent_le _ _
    (amplitudeLatitudeCoefficient_nonneg μ p₀ s hr) ht hz

/-- The fixed original source atom, also at negative physical latitudes. -/
def amplitudeDiracAtom (r : ℝ) : ℝ := |r|/(1+|r|)

theorem amplitudeDiracAtom_continuous : Continuous amplitudeDiracAtom := by
  unfold amplitudeDiracAtom
  exact continuous_abs.div (continuous_const.add continuous_abs) (fun r => by positivity)

theorem amplitudeDiracAtom_mem (r : ℝ) : amplitudeDiracAtom r∈Ico (0 : ℝ) 1 := by
  have hd : 0<1+|r| := by positivity
  exact ⟨div_nonneg (abs_nonneg r) hd.le,(div_lt_one hd).mpr (by linarith)⟩

theorem amplitudeDiracAtom_lower {δ r : ℝ} (hδ : 0<δ) (hr : δ≤|r|) :
    δ/(1+δ)≤amplitudeDiracAtom r := by
  have hd : 0<1+δ := by linarith
  have hrp : 0<1+|r| := by positivity
  unfold amplitudeDiracAtom
  apply (div_le_div_iff₀ hd hrp).mpr
  nlinarith

def amplitudeDiracTangentDeficit (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r z : ℝ) : ℝ :=
  amplitudeLatitudeCovariance μ p₀ s r (amplitudeDiracAtom r)+
    amplitudeLatitudeCovarianceFirst μ p₀ s r (amplitudeDiracAtom r)*(z-amplitudeDiracAtom r)-
      amplitudeLatitudeCovariance μ p₀ s r z

theorem amplitudeDiracTangentDeficit_joint_continuous (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) :
    Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => amplitudeDiracTangentDeficit μ p₀ z.1.1 z.1.2 z.2) := by
  have hB (i : BankIndex μ) : Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ =>
      amplitudeLatitudeCoefficient μ p₀ z.1.1 z.1.2 i) :=
    (amplitudeLatitudeCoefficient_joint_continuous μ p₀ i).comp continuous_fst
  have hA : Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => amplitudeDiracAtom z.1.2) :=
    amplitudeDiracAtom_continuous.comp (continuous_snd.comp continuous_fst)
  have hC : Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ =>
      amplitudeLatitudeCovariance μ p₀ z.1.1 z.1.2 (amplitudeDiracAtom z.1.2)) := by
    simp only [amplitudeLatitudeCovariance_eq_polynomial,FiniteNonnegativePolynomial.covariance]
    exact continuous_finsetSum _ fun i _ => (hB i).mul (hA.pow _)
  have hD : Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ =>
      amplitudeLatitudeCovarianceFirst μ p₀ z.1.1 z.1.2 (amplitudeDiracAtom z.1.2)) := by
    unfold amplitudeLatitudeCovarianceFirst FiniteNonnegativePolynomial.firstDerivative
    exact continuous_finsetSum _ fun i _ => ((hB i).mul continuous_const).mul (hA.pow _)
  have hZ : Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ =>
      amplitudeLatitudeCovariance μ p₀ z.1.1 z.1.2 z.2) := by
    simp only [amplitudeLatitudeCovariance_eq_polynomial,FiniteNonnegativePolynomial.covariance]
    exact continuous_finsetSum _ fun i _ => (hB i).mul (continuous_snd.pow _)
  exact (hC.add (hD.mul (continuous_snd.sub hA))).sub hZ

/-- Actual amplitude and latitude covariance error constants are selected
before every dimension and Gaussian bank. All amplitudes in [-2,2] are
allowed; no original or perturbed pressure conclusion is supplied. -/
theorem exists_uniform_amplitudeDiracTangentDeficit_bound (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) {δ ρ : ℝ} (hδ : 0<δ) (hδρ : δ≤ρ) (hρ : ρ<1) :
    ∃ η C : ℝ,0<η ∧ η≤1 ∧ 0≤C ∧ ∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ r : ℝ,|r|∈Icc δ ρ → ∀ z∈Icc (-1 : ℝ) 1,
        amplitudeDiracTangentDeficit μ p₀ s r z≤C*({t : ℝ | t< -η}.indicator (fun _ => (1 : ℝ))) z := by
  let η := δ/(1+δ)
  have hη : 0<η := by dsimp [η];positivity
  have hη1 : η≤1 := by
    dsimp [η]
    apply (div_le_one (by linarith : 0<1+δ)).mpr
    linarith
  obtain ⟨B,hB⟩ := (((isCompact_Icc (a := fun _ : Fin 2 => (-2 : ℝ)) (b := fun _ => (2 : ℝ))).prod
    (isCompact_Icc (a := -ρ) (b := ρ))).prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      (amplitudeDiracTangentDeficit_joint_continuous μ p₀).continuousOn
  refine ⟨η,max B 0,hη,hη1,le_max_right _ _,?_⟩
  intro s hs r hr z hz
  by_cases hneg : z< -η
  · rw [indicator_of_mem (show z∈{t : ℝ | t< -η} from hneg),mul_one]
    have hsI : s∈Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => (2 : ℝ)) := by
      constructor
      · intro j;exact (abs_le.mp (hs j)).1
      · intro j;exact (abs_le.mp (hs j)).2
    have hrI : r∈Icc (-ρ) ρ := abs_le.mp hr.2
    have hh : |amplitudeDiracTangentDeficit μ p₀ s r z|≤B := by
      simpa only [Real.norm_eq_abs] using hB ((s,r),z) ⟨⟨hsI,hrI⟩,hz⟩
    exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
  · rw [indicator_of_notMem (show z∉{t : ℝ | t< -η} from hneg),mul_zero]
    have ha := amplitudeDiracAtom_lower hδ hr.1
    have hh := amplitudeLatitudeCovariance_tangent_le μ p₀ s (hr.2.trans hρ.le)
      (amplitudeDiracAtom_mem r).1 (show -amplitudeDiracAtom r≤z by linarith [le_of_not_gt hneg])
    unfold amplitudeDiracTangentDeficit
    linarith

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
