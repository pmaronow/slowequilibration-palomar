-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ValueObservationSmallOverlap

/-! Literal physical mixed and proper pure pair conditioning targets. -/
@[expose] public section
namespace SlowEquilibration.PairObservationTargets
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma hilbertPair_norm_le_sum {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (w : WithLp 2 (E×F)) :
    ‖w‖ ≤ ‖w.fst‖+‖w.snd‖ := by
  have h:=WithLp.prod_norm_sq_eq_of_L2 w
  nlinarith [norm_nonneg w,norm_nonneg w.fst,norm_nonneg w.snd,
    mul_nonneg (norm_nonneg w.fst) (norm_nonneg w.snd)]

def mixedPointTarget (N m : ℕ) (h k : ℝ) : MixedObservationSpace m :=
  WithLp.toLp 2 (WithLp.toLp 2 ![Real.sqrt (N:ℝ)*h,Real.sqrt (N:ℝ)*k],0)

def mixedPairTarget (N m : ℕ) (h1 k1 h2 k2 : ℝ) :
    WithLp 2 (MixedObservationSpace m×MixedObservationSpace m) :=
  WithLp.toLp 2 (mixedPointTarget N m h1 k1,mixedPointTarget N m h2 k2)

def valuePointTarget (N m : ℕ) (h : ℝ) : ValueObservationSpace m :=
  WithLp.toLp 2 (Real.sqrt (N:ℝ)*h,0)

def valuePairTarget (N m : ℕ) (h1 h2 : ℝ) :
    WithLp 2 (ValueObservationSpace m×ValueObservationSpace m) :=
  WithLp.toLp 2 (valuePointTarget N m h1,valuePointTarget N m h2)

lemma mixedPointTarget_norm_le (N m : ℕ) {M h k : ℝ} (hh : |h| ≤ M) (hk : |k| ≤ M) :
    ‖mixedPointTarget N m h k‖ ≤ 2*M*Real.sqrt (N:ℝ) := by
  let a:=Real.sqrt (N:ℝ)*h
  let b:=Real.sqrt (N:ℝ)*k
  have hab : ‖(WithLp.toLp 2 ![a,b] : EuclideanSpace ℝ (Fin 2))‖ ≤ |a|+|b| := by
    have hs:=PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (WithLp.toLp 2 ![a,b] : EuclideanSpace ℝ (Fin 2))
    simp only [Fin.sum_univ_two,Real.norm_eq_abs,Matrix.cons_val_zero,Matrix.cons_val_one,
      sq_abs] at hs
    nlinarith [norm_nonneg (WithLp.toLp 2 ![a,b] : EuclideanSpace ℝ (Fin 2)),abs_nonneg a,abs_nonneg b,
      mul_nonneg (abs_nonneg a) (abs_nonneg b),sq_abs a,sq_abs b]
  have hpair:=hilbertPair_norm_le_sum (mixedPointTarget N m h k)
  change ‖mixedPointTarget N m h k‖ ≤ ‖(WithLp.toLp 2 ![a,b] : EuclideanSpace ℝ (Fin 2))‖+‖(0 : EuclideanSpace ℝ (Fin m))‖ at hpair
  rw [norm_zero,add_zero] at hpair
  calc
    _ ≤ |a|+|b| := hpair.trans hab
    _ ≤ Real.sqrt (N:ℝ)*M+Real.sqrt (N:ℝ)*M := by
      dsimp only [a,b]
      rw [abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      gcongr
    _ = _ := by ring

lemma mixedPairTarget_norm_le (N m : ℕ) {M h1 k1 h2 k2 : ℝ}
    (hh1 : |h1| ≤ M) (hk1 : |k1| ≤ M) (hh2 : |h2| ≤ M) (hk2 : |k2| ≤ M) :
    ‖mixedPairTarget N m h1 k1 h2 k2‖ ≤ 4*M*Real.sqrt (N:ℝ) := by
  exact (hilbertPair_norm_le_sum _).trans
    ((add_le_add (mixedPointTarget_norm_le N m hh1 hk1) (mixedPointTarget_norm_le N m hh2 hk2)).trans_eq (by ring))

lemma valuePairTarget_norm_le (N m : ℕ) {M h1 h2 : ℝ}
    (hh1 : |h1| ≤ M) (hh2 : |h2| ≤ M) :
    ‖valuePairTarget N m h1 h2‖ ≤ 2*M*Real.sqrt (N:ℝ) := by
  have hsingle {h : ℝ} (hh : |h| ≤ M) : ‖valuePointTarget N m h‖ ≤ M*Real.sqrt (N:ℝ) := by
    have hp:=hilbertPair_norm_le_sum (valuePointTarget N m h)
    change ‖valuePointTarget N m h‖ ≤ ‖Real.sqrt (N:ℝ)*h‖+‖(0 : EuclideanSpace ℝ (Fin m))‖ at hp
    rw [norm_zero,add_zero,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans_eq (by ring))
  exact (hilbertPair_norm_le_sum _).trans ((add_le_add (hsingle hh1) (hsingle hh2)).trans_eq (by ring))

end
end SlowEquilibration.PairObservationTargets
