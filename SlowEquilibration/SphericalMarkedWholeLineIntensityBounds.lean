-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeometricPrefactorBounds
public import SlowEquilibration.SphericalOnePointRadialCurvature
public import SlowEquilibration.GOEPhysicalLeadingUpper
public import SlowEquilibration.GOECrudeDeterminant

/-! Genuine compact whole-line and Gaussian-score-damped global upper bounds
for the actual original mixed one-point Kac--Rice intensity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory Filter SphericalModel SphericalSequentialRegression
open GOEPhysicalPotential GaussianCrudeDeterminant
open scoped ENNReal
set_option maxHeartbeats 400000

def sourceScoreDenominator (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  2*Real.pi*Real.sqrt (μ.scoreCovariance Q).det

theorem sourceScoreDenominator_pos (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) : 0 < sourceScoreDenominator μ Q :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.sqrt_pos.mpr (μ.scoreCovariance_det_pos hQ hnp))

theorem sourceSphereKRPrefactor_upper (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (sphereKRPrefactor (n+1) μ Q).toReal ≤
        C*Real.exp ((n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)) := by
  obtain ⟨B,_,hB⟩ := sphereKRPrefactor_log_error_bound μ hQ
  refine ⟨Real.exp B,Real.exp_pos _,?_⟩
  intro n
  have hpos := ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
    (sphereKRPrefactor_ne_top (n+1) μ Q)
  have hh := (abs_le.mp (hB n)).2
  have he : Real.log (sphereKRPrefactor (n+1) μ Q).toReal ≤
      B+(n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2) := by linarith
  have hx := Real.exp_le_exp.mpr he
  rw [Real.exp_log hpos,Real.exp_add] at hx
  exact hx

theorem sourceMixedIntensity_eq_ofReal (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k : ℝ) :
    mixedCriticalIntensity n μ Q (scorePairEquiv (e,k))=
      ENNReal.ofReal ((sphereKRPrefactor (n+1) μ Q).toReal*
        ((n+2 : ℕ)/sourceScoreDenominator μ Q)*
        Real.exp (-(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k)))*
        physicalMean n (n+2) (Q^2*μ.xi2 Q) k) := by
  have hp : 0 ≤ (sphereKRPrefactor (n+1) μ Q).toReal := ENNReal.toReal_nonneg
  have hd : 0 ≤ ((n+2 : ℕ) : ℝ)/sourceScoreDenominator μ Q :=
    div_nonneg (by positivity) (sourceScoreDenominator_pos μ hQ hnp).le
  unfold mixedCriticalIntensity physicalScorePdf
  conv_lhs => rw [←ENNReal.ofReal_toReal (sphereKRPrefactor_ne_top (n+1) μ Q)]
  change ENNReal.ofReal ((sphereKRPrefactor (n+1) μ Q).toReal)*
    ENNReal.ofReal (((n+2 : ℕ) : ℝ)/sourceScoreDenominator μ Q*
      Real.exp (-(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k))))*
    ENNReal.ofReal (physicalMean n (n+2) (Q^2*μ.xi2 Q) k)=_
  rw [←ENNReal.ofReal_mul hp,←ENNReal.ofReal_mul (mul_nonneg hp (mul_nonneg hd (Real.exp_pos _).le))]
  congr 1
  ring

/-- One constant is fixed before every compact radial cutoff and every
positive rate error. Energy is unrestricted and shifts include the GOE bulk. -/
theorem sourceMixedIntensity_compact_upper (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ B : ℝ, 0 < B ∧ ∀ {Z eps : ℝ}, 0 ≤ Z → 0 < eps →
      ∀ᶠ n : ℕ in atTop, ∀ e k : ℝ, |k| ≤ Z →
        mixedCriticalIntensity n μ Q (scorePairEquiv (e,k)) ≤
          ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((n+2 : ℕ)*
            (sourceRadialProfile μ Q e k+eps))) := by
  have ha := mul_pos hQ (μ.xi1_pos hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hD := sourceScoreDenominator_pos μ hQ hnp
  obtain ⟨C,hC,hgeo⟩ := sourceSphereKRPrefactor_upper μ hQ
  refine ⟨C/sourceScoreDenominator μ Q*Real.exp ((1+|Real.log (Q^2*μ.xi2 Q)|)/2),
    by positivity,?_⟩
  intro Z eps hZ heps
  filter_upwards [GOEPhysicalLeadingUpper.physical_mean_leading_upper_uniform 1 hb hZ heps] with n hn
  intro e k hk
  rw [sourceMixedIntensity_eq_ofReal n μ hQ hnp e k]
  apply ENNReal.ofReal_le_ofReal
  let E := -(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k))
  have hm : 0 ≤ physicalMean n (n+2) (Q^2*μ.xi2 Q) k := integral_nonneg (fun _ => abs_nonneg _)
  have hP := mul_le_mul (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hgeo n) (show 0 ≤ ((n+2 : ℕ) : ℝ)/sourceScoreDenominator μ Q by positivity))
      (Real.exp_pos E).le) (hn k hk) hm (by positivity)
  apply hP.trans_eq
  have hexp : (n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)+E+
      ((n+2 : ℕ)*(Real.log (Q^2*μ.xi2 Q)/2+
        SemicirclePotential.potential (k/Real.sqrt (Q^2*μ.xi2 Q))+eps)+
          (1 : ℝ)*(1+|Real.log (Q^2*μ.xi2 Q)|)/2)=
      (n+2 : ℕ)*(sourceRadialProfile μ Q e k+eps)+(1+|Real.log (Q^2*μ.xi2 Q)|)/2 := by
    unfold sourceRadialProfile markedComplexity
    rw [Real.log_div hb.ne' ha.ne']
    dsimp [E]
    rw [scorePairEquiv_apply]
    simp only [Matrix.cons_val_one,Matrix.cons_val_fin_one]
    ring
  calc
    _=(C/sourceScoreDenominator μ Q*(n+2 : ℕ))*Real.exp
      ((n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)+E+
        ((n+2 : ℕ)*(Real.log (Q^2*μ.xi2 Q)/2+
          SemicirclePotential.potential (k/Real.sqrt (Q^2*μ.xi2 Q))+eps)+
            (1 : ℝ)*(1+|Real.log (Q^2*μ.xi2 Q)|)/2)) := by
      simp only [Real.exp_add]
      ring
    _=_ := by rw [hexp,Real.exp_add]; ring

/-- Genuine unrestricted radial tails are controlled by the original score
quadratic form and the proved GOE determinant bound, in every dimension. -/
theorem sourceMixedIntensity_crude_upper (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, ∀ e k : ℝ,
      mixedCriticalIntensity n μ Q (scorePairEquiv (e,k)) ≤
        ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((n+2 : ℕ)*
          ((1-Real.log (Q*μ.xi1 Q))/2+crudeConstant (Q^2*μ.xi2 Q)+|k|-
            scoreQuadratic μ Q (scorePairEquiv (e,k))/2))) := by
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hD := sourceScoreDenominator_pos μ hQ hnp
  obtain ⟨C,hC,hgeo⟩ := sourceSphereKRPrefactor_upper μ hQ
  refine ⟨C/sourceScoreDenominator μ Q,by positivity,?_⟩
  intro n e k
  rw [sourceMixedIntensity_eq_ofReal n μ hQ hnp e k]
  apply ENNReal.ofReal_le_ofReal
  let E := -(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k))
  have hm : 0 ≤ physicalMean n (n+2) (Q^2*μ.xi2 Q) k := integral_nonneg (fun _ => abs_nonneg _)
  have hP := mul_le_mul (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hgeo n) (show 0 ≤ ((n+2 : ℕ) : ℝ)/sourceScoreDenominator μ Q by positivity))
      (Real.exp_pos E).le)
    (GOECrudeDeterminant.physical_crude_mean n (n+2) (by omega) hb k).2 hm (by positivity)
  apply hP.trans_eq
  have hexp : (n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)+E+
      (n+2 : ℕ)*(crudeConstant (Q^2*μ.xi2 Q)+|k|)=
      (n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2+crudeConstant (Q^2*μ.xi2 Q)+|k|-
        scoreQuadratic μ Q (scorePairEquiv (e,k))/2) := by dsimp [E]; ring
  calc
    _=(C/sourceScoreDenominator μ Q*(n+2 : ℕ))*Real.exp
      ((n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)+E+
        (n+2 : ℕ)*(crudeConstant (Q^2*μ.xi2 Q)+|k|)) := by
      simp only [Real.exp_add]
      ring
    _=_ := by rw [hexp]

end SlowEquilibration.SphericalMarkedWindows
