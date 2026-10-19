-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetFeatures

@[expose] public section
namespace SlowEquilibration.PureTensorJetBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel PureTensorJetFeatures
open GaussianCompactMaximum GaussianCompactFeatureComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two signs used to represent an absolute supremum. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem norm_sign (b : Bool) : ‖sign b‖ = 1 := by cases b <;> norm_num [sign]
@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := norm_sign b

def signJoin {κ : Type*} [Fintype κ] (s : ℝ) (z : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (Unit ⊕ κ) := WithLp.toLp 2 (Sum.elim (fun _ => s) z)

theorem signJoin_norm_sq {κ : Type*} [Fintype κ] (s : ℝ) (z : EuclideanSpace ℝ κ) :
    ‖signJoin s z‖ ^ 2 = s ^ 2 + ‖z‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, signJoin, Fintype.sum_sum_type]

theorem signJoin_sub {κ : Type*} [Fintype κ] (s t : ℝ) (z w : EuclideanSpace ℝ κ) :
    signJoin s z - signJoin t w = signJoin (s - t) (z - w) := by
  ext (i | i) <;> rfl

theorem signJoin_fst_le {κ : Type*} [Fintype κ] (s : ℝ) (z : EuclideanSpace ℝ κ) :
    |s| ≤ ‖signJoin s z‖ := by
  have h := signJoin_norm_sq s z
  nlinarith [norm_nonneg (signJoin s z), sq_nonneg ‖z‖, sq_abs s]

theorem signJoin_snd_le {κ : Type*} [Fintype κ] (s : ℝ) (z : EuclideanSpace ℝ κ) :
    ‖z‖ ≤ ‖signJoin s z‖ := by
  have h := signJoin_norm_sq s z
  nlinarith [norm_nonneg (signJoin s z), sq_nonneg s]

theorem signJoin_continuous {κ : Type*} [Fintype κ] :
    Continuous (fun z : ℝ × EuclideanSpace ℝ κ => signJoin z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i <;> dsimp only [Sum.elim] <;> fun_prop

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [TopologicalSpace V] [CompactSpace V] [Nonempty V]

def signedFeature (a : V → EuclideanSpace ℝ ι) (v : Bool × V) :
    EuclideanSpace ℝ ι := sign v.1 • a v.2

def signedComparison (z : V → EuclideanSpace ℝ κ) (M P : ℝ) (v : Bool × V) :
    EuclideanSpace ℝ (Unit ⊕ κ) := (2 * M * P) • signJoin (sign v.1) (z v.2)

theorem signedFeature_continuous (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Continuous (signedFeature a) := by
  exact ((continuous_of_discreteTopology : Continuous sign).comp continuous_fst).smul
    (ha.comp continuous_snd)

theorem signedComparison_continuous (z : V → EuclideanSpace ℝ κ) (hz : Continuous z)
    (M P : ℝ) : Continuous (signedComparison z M P) := by
  unfold signedComparison
  have hh := signJoin_continuous.comp
    (((continuous_of_discreteTopology : Continuous sign).comp continuous_fst).prodMk
      (hz.comp continuous_snd))
  convert hh.const_smul (2 * M * P) using 1
  funext v
  rfl

/-- Adding one sign coordinate controls the absolute supremum at a fixed
universal cost. -/
theorem signedFeature_increment_le (a : V → EuclideanSpace ℝ ι)
    (z : V → EuclideanSpace ℝ κ) {M P : ℝ} (hM : 0 ≤ M) (hP : 1 ≤ P)
    (ha : ∀ v, ‖a v‖ ≤ M)
    (hinc : ∀ v w, ‖a v - a w‖ ≤ M * P * ‖z v - z w‖) (v w : Bool × V) :
    ‖signedFeature a v - signedFeature a w‖ ≤
      ‖signedComparison z M P v - signedComparison z M P w‖ := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have he : signedFeature a v - signedFeature a w =
      sign v.1 • (a v.2 - a w.2) + (sign v.1 - sign w.1) • a w.2 := by
    simp only [signedFeature, smul_sub, sub_smul]
    abel
  have hfirst := signJoin_fst_le (sign v.1 - sign w.1) (z v.2 - z w.2)
  have hsecond := signJoin_snd_le (sign v.1 - sign w.1) (z v.2 - z w.2)
  have hnorm : ‖signedFeature a v - signedFeature a w‖ ≤
      M * P * ‖z v.2 - z w.2‖ + M * |sign v.1 - sign w.1| := by
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs, abs_sign, one_mul]
    exact add_le_add (hinc _ _) (by nlinarith [abs_nonneg (sign v.1 - sign w.1), ha w.2])
  have hmono : M * |sign v.1 - sign w.1| ≤ M * P * |sign v.1 - sign w.1| := by
    gcongr
    exact le_mul_of_one_le_right hM hP
  have htot : ‖signedFeature a v - signedFeature a w‖ ≤
      2 * M * P * ‖signJoin (sign v.1 - sign w.1) (z v.2 - z w.2)‖ := by
    calc
      _ ≤ M * P * ‖z v.2 - z w.2‖ + M * P * |sign v.1 - sign w.1| :=
        hnorm.trans (add_le_add le_rfl hmono)
      _ ≤ M * P * ‖signJoin (sign v.1 - sign w.1) (z v.2 - z w.2)‖ +
          M * P * ‖signJoin (sign v.1 - sign w.1) (z v.2 - z w.2)‖ := by gcongr
      _ = _ := by ring
  simpa only [signedComparison, ← smul_sub, signJoin_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ 2 * M * P by positivity)] using htot

/-- The signed supremum is the actual absolute supremum. -/
def absoluteSupremum (a : V → EuclideanSpace ℝ ι) (g : EuclideanSpace ℝ ι) : ℝ :=
  ⨆ v : Bool × V, inner ℝ (signedFeature a v) g

theorem supremum_integrable_of_continuous
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L) :
    Integrable (fun g => ⨆ v, L v g) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨K, hK, hb⟩ := exists_feature_bound L hL
  apply (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K).mono'
    (field_supremum_lipschitz L hb).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_field_supremum_le L hb)

theorem absoluteSupremum_integrable (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Integrable (absoluteSupremum a) (SYK.standardGaussianMeasureOnEuclidean ι) :=
  supremum_integrable_of_continuous
    (fun v : Bool × V => innerSL ℝ (signedFeature a v))
    ((innerSL ℝ).continuous.comp (signedFeature_continuous a ha))

/-- Expected absolute supremum from the actual finite Gaussian comparison,
with both coefficient spaces and their dimensions explicit. -/
theorem expected_absoluteSupremum_le (a : V → EuclideanSpace ℝ ι)
    (z : V → EuclideanSpace ℝ κ) (ha : Continuous a) (hz : Continuous z)
    {M P Q : ℝ} (hM : 0 ≤ M) (hP : 1 ≤ P) (hQ : 0 ≤ Q)
    (hab : ∀ v, ‖a v‖ ≤ M) (hzb : ∀ v, ‖z v‖ ^ 2 ≤ Q)
    (hinc : ∀ v w, ‖a v - a w‖ ≤ M * P * ‖z v - z w‖) :
    (∫ g, absoluteSupremum a g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      2 * M * P * Real.sqrt (1 + Q) * Real.sqrt (1 + (Fintype.card κ : ℝ)) := by
  let b := signedComparison z M P
  have hb := signedComparison_continuous z hz M P
  have hcomp := expected_supremum_comparison_of_increment_norm
    (signedFeature a) b (signedFeature_continuous a ha) hb
    (signedFeature_increment_le a z hM hP hab hinc)
  let K : ℝ := 2 * M * P * Real.sqrt (1 + Q)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbnorm (v : Bool × V) : ‖b v‖ ≤ K := by
    change ‖(2 * M * P) • signJoin (sign v.1) (z v.2)‖ ≤ K
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [signJoin_norm_sq, Real.sq_sqrt (by positivity)]
    have hs : sign v.1 ^ 2 = 1 := by cases v.1 <;> norm_num [sign]
    rw [hs]
    linarith [hzb v.2]
  have hL (v : Bool × V) : ‖innerSL ℝ (b v)‖ ≤ K := by
    simpa using hbnorm v
  have hbint : Integrable (fun g => ⨆ v : Bool × V, inner ℝ (b v) g)
      (SYK.standardGaussianMeasureOnEuclidean (Unit ⊕ κ)) :=
    supremum_integrable_of_continuous (fun v : Bool × V => innerSL ℝ (b v))
      ((innerSL ℝ).continuous.comp hb)
  have henv := integral_mono hbint
    (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K) (fun g => by
      exact (le_abs_self _).trans (norm_field_supremum_le
        (fun v : Bool × V => innerSL ℝ (b v)) hL g))
  rw [integral_const_mul] at henv
  have hg := GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card (Unit ⊕ κ)
  have hcard : (Fintype.card (Unit ⊕ κ) : ℝ) = 1 + (Fintype.card κ : ℝ) := by simp
  rw [hcard] at hg
  exact hcomp.trans (henv.trans (mul_le_mul_of_nonneg_left hg hK))

theorem norm_inner_le_absoluteSupremum (a : V → EuclideanSpace ℝ ι)
    (ha : Continuous a) (g : EuclideanSpace ℝ ι) (v : V) :
    |inner ℝ (a v) g| ≤ absoluteSupremum a g := by
  have hL := (innerSL ℝ).continuous.comp (signedFeature_continuous a ha)
  obtain ⟨K, _, hK⟩ := exists_feature_bound
    (fun w : Bool × V => innerSL ℝ (signedFeature a w)) hL
  have hp := le_field_supremum (fun w : Bool × V => innerSL ℝ (signedFeature a w))
    hK g (true, v)
  have hm := le_field_supremum (fun w : Bool × V => innerSL ℝ (signedFeature a w))
    hK g (false, v)
  apply abs_le.mpr
  constructor
  · have hm' : -inner ℝ (a v) g ≤ absoluteSupremum a g := by
      simpa only [absoluteSupremum, innerSL_apply_apply, signedFeature, sign, Bool.false_eq_true,
        ite_false, neg_one_smul, inner_neg_left] using hm
    linarith
  · simpa only [absoluteSupremum, innerSL_apply_apply, signedFeature, sign, ite_true,
      one_smul] using hp

theorem absoluteSupremum_nonneg (a : V → EuclideanSpace ℝ ι)
    (ha : Continuous a) (g : EuclideanSpace ℝ ι) : 0 ≤ absoluteSupremum a g :=
  (abs_nonneg _).trans (norm_inner_le_absoluteSupremum a ha g (Classical.choice inferInstance))

abbrev UnitSphere (N : ℕ) := Metric.sphere (0 : Vector N) 1
abbrev UnitBlocks (N j : ℕ) := Fin (j + 1) → UnitSphere N

instance unitSphere_nonempty (N : ℕ) [NeZero N] : Nonempty (UnitSphere N) :=
  (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort

def unitInsertion (N p j : ℕ) (v : UnitBlocks N j) :
    EuclideanSpace ℝ (TensorIndex N p) := insertionFeature (fun k => (v k).val)

theorem unitInsertion_continuous (N p j : ℕ) : Continuous (unitInsertion N p j) :=
  (insertionFeature_continuous N p j).comp
    (continuous_pi (fun k => continuous_subtype_val.comp (continuous_apply k)))

theorem unit_norm {N : ℕ} (v : UnitSphere N) : ‖(v : Vector N)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using v.property

/-- An integrable, genuine uniform envelope for the unnormalized pure tensor jet.
The index is only one spatial unit vector and `j` unit derivative directions. -/
def unitJetEnvelope (N p j : ℕ) (J : Disorder N p) : ℝ :=
  absoluteSupremum (unitInsertion N p j) (WithLp.toLp 2 J)

theorem unitJetEnvelope_integrable {N p j : ℕ} (hN : 0 < N) :
    Integrable (unitJetEnvelope N p j) (disorderLaw N p) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h := absoluteSupremum_integrable (unitInsertion N p j)
    (unitInsertion_continuous N p j)
  have hm : MeasurePreserving (WithLp.toLp 2 : Disorder N p →
      EuclideanSpace ℝ (TensorIndex N p)) (disorderLaw N p)
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N p)) :=
    ⟨by fun_prop, rfl⟩
  exact (hm.integrable_comp h.aestronglyMeasurable).mpr h

theorem unitJetEnvelope_nonneg {N p j : ℕ} (hN : 0 < N) (J : Disorder N p) :
    0 ≤ unitJetEnvelope N p j J := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact absoluteSupremum_nonneg _ (unitInsertion_continuous N p j) _

/-- The dimension-free-in-degree Gaussian tensor-jet estimate before the
Hamiltonian's physical radius normalization. -/
theorem expected_unitJetEnvelope_le {N p j : ℕ} (hN : 0 < N) (hp : 1 ≤ p) :
    (∫ J, unitJetEnvelope N p j J ∂disorderLaw N p) ≤
      2 * ((j : ℝ) + 2) * (p : ℝ) ^ j * Real.sqrt p * Real.sqrt N := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let z : UnitBlocks N j → EuclideanSpace ℝ (Fin (j + 1) × Fin N) :=
    fun v => blockFeature (fun k => (v k).val)
  have hz : Continuous z := (blockFeature_continuous N (j + 1)).comp
    (continuous_pi (fun k => continuous_subtype_val.comp (continuous_apply k)))
  have hp' : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)]
    exact_mod_cast hp
  have h := expected_absoluteSupremum_le (unitInsertion N p j) z
    (unitInsertion_continuous N p j) hz (M := (p : ℝ) ^ j) (P := Real.sqrt p)
    (Q := (j : ℝ) + 1) (by positivity) hp' (by positivity)
    (fun v => insertionFeature_norm_le _ (fun k => unit_norm (v k)))
    (fun v => by simp [z, blockFeature_norm_sq, unit_norm])
    (fun v w => insertionFeature_increment_le _ _ (fun k => unit_norm (v k))
      (fun k => unit_norm (w k)))
  have hcard : (Fintype.card (Fin (j + 1) × Fin N) : ℝ) = ((j : ℝ) + 1) * N := by
    simp
  rw [hcard] at h
  have hdim : 1 + ((j : ℝ) + 1) * N ≤ ((j : ℝ) + 2) * N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hsqrt : Real.sqrt (1 + ((j : ℝ) + 1) * N) ≤
      Real.sqrt ((j : ℝ) + 2) * Real.sqrt N := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hdim
  have hnum : 2 * (p : ℝ) ^ j * Real.sqrt p * Real.sqrt (1 + ((j : ℝ) + 1)) *
      Real.sqrt (1 + ((j : ℝ) + 1) * N) ≤
      2 * ((j : ℝ) + 2) * (p : ℝ) ^ j * Real.sqrt p * Real.sqrt N := by
    have harg : 1 + ((j : ℝ) + 1) = (j : ℝ) + 2 := by ring
    rw [harg]
    calc
      _ ≤ 2 * (p : ℝ) ^ j * Real.sqrt p * Real.sqrt ((j : ℝ) + 2) *
          (Real.sqrt ((j : ℝ) + 2) * Real.sqrt N) := by gcongr
      _ = _ := by rw [← mul_assoc, mul_assoc (2 * (p : ℝ) ^ j * Real.sqrt p),
        Real.mul_self_sqrt (by positivity)]; ring
  have hLaw : HasLaw (WithLp.toLp 2 : Disorder N p →
      EuclideanSpace ℝ (TensorIndex N p))
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N p)) (disorderLaw N p) :=
    ⟨by fun_prop, rfl⟩
  have hi := hLaw.integral_comp
    (absoluteSupremum_integrable _ (unitInsertion_continuous N p j)).aestronglyMeasurable
  change (∫ J, unitJetEnvelope N p j J ∂disorderLaw N p) = _ at hi
  rw [hi]
  exact h.trans hnum

theorem unitJetEnvelope_continuous {N p j : ℕ} (hN : 0 < N) :
    Continuous (unitJetEnvelope N p j) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let L := fun v : Bool × UnitBlocks N j =>
    innerSL ℝ (signedFeature (unitInsertion N p j) v)
  have hL : Continuous L := (innerSL ℝ).continuous.comp
    (signedFeature_continuous _ (unitInsertion_continuous N p j))
  obtain ⟨K, _, hb⟩ := exists_feature_bound L hL
  exact (field_supremum_lipschitz L hb).continuous.comp (by fun_prop)

theorem norm_insertion_le_unitJetEnvelope {N p j : ℕ} (hN : 0 < N)
    (v : Fin (j + 1) → Vector N) (hv : ∀ k, ‖v k‖ = 1) (J : Disorder N p) :
    |inner ℝ (insertionFeature (p := p) v) (WithLp.toLp 2 J)| ≤
      unitJetEnvelope N p j J := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let w : UnitBlocks N j := fun k => ⟨v k, by
    simpa only [Metric.mem_sphere, dist_zero_right] using hv k⟩
  exact norm_inner_le_absoluteSupremum _ (unitInsertion_continuous N p j) _ w

/-- The physical uniform envelope of the original Hamiltonian's actual `j`th
Fréchet derivative on the radius-`sqrt N` ball. -/
def pureJetEnvelope (N p j : ℕ) (J : Disorder N p) : ℝ :=
  normalization N p * Real.sqrt N ^ (p - j) * unitJetEnvelope N p j J

theorem pureJetEnvelope_nonneg {N p j : ℕ} (hN : 0 < N) (J : Disorder N p) :
    0 ≤ pureJetEnvelope N p j J := by
  unfold pureJetEnvelope
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (pow_nonneg (Real.sqrt_nonneg _) _)) (unitJetEnvelope_nonneg hN J)

theorem pureJetEnvelope_integrable {N p j : ℕ} (hN : 0 < N) :
    Integrable (pureJetEnvelope N p j) (disorderLaw N p) :=
  (unitJetEnvelope_integrable hN).const_mul _

theorem pureJetEnvelope_continuous {N p j : ℕ} (hN : 0 < N) :
    Continuous (pureJetEnvelope N p j) :=
  continuous_const.mul (unitJetEnvelope_continuous hN)

theorem exists_unit_scale {N : ℕ} (hN : 0 < N) (x : Vector N) :
    ∃ u : UnitSphere N, x = ‖x‖ • (u : Vector N) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  by_cases hx : x = 0
  · exact ⟨Classical.choice inferInstance, by simp [hx]⟩
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    refine ⟨⟨‖x‖⁻¹ • x, ?_⟩, ?_⟩
    · simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hn]
    · simp only [smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- A genuine uniform bound on the operator norm of the actual iterated
Fréchet derivative, including order zero. -/
theorem iteratedFDeriv_norm_le_pureJetEnvelope {N p j : ℕ} (hN : 0 < N)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    ‖iteratedFDeriv ℝ j (Hamiltonian N p J) x‖ ≤ pureJetEnvelope N p j J := by
  have hnormal : 0 ≤ normalization N p := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hnonneg : 0 ≤ unitJetEnvelope N p j J := unitJetEnvelope_nonneg hN J
  apply SphericalAging.GaussianLandscape.multilinear_norm_le_of_unit_bound _
    (pureJetEnvelope_nonneg hN J)
  intro a ha
  obtain ⟨u, hu⟩ := exists_unit_scale hN x
  have hv : ∀ k : Fin (j + 1), ‖(Fin.cons (u : Vector N) a : Fin (j + 1) → Vector N) k‖ = 1 := by
    intro k
    refine Fin.cases (unit_norm u) (fun i => ?_) k
    exact ha i
  have henv := norm_insertion_le_unitJetEnvelope hN (Fin.cons (u : Vector N) a) hv J
  rw [Hamiltonian_iteratedFDeriv_eq_inner, hu, insertionFeature_cons_smul,
    inner_smul_left, conj_trivial]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (show 0 ≤ normalization N p from Real.rpow_nonneg (Nat.cast_nonneg N) _),
    abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  unfold pureJetEnvelope
  calc
    _ ≤ normalization N p * (‖x‖ ^ (p - j) * unitJetEnvelope N p j J) := by
      gcongr
    _ ≤ normalization N p * (Real.sqrt N ^ (p - j) * unitJetEnvelope N p j J) := by
      gcongr
    _ = _ := by ring

/-- The expected physical envelope, still displaying the exact original
normalization and radius power. -/
theorem expected_pureJetEnvelope_le_normalized {N p j : ℕ}
    (hN : 0 < N) (hp : 1 ≤ p) :
    (∫ J, pureJetEnvelope N p j J ∂disorderLaw N p) ≤
      normalization N p * Real.sqrt N ^ (p - j) *
        (2 * ((j : ℝ) + 2) * (p : ℝ) ^ j * Real.sqrt p * Real.sqrt N) := by
  unfold pureJetEnvelope
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (expected_unitJetEnvelope_le hN hp)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (pow_nonneg (Real.sqrt_nonneg _) _))

theorem physical_normalization_identity {N p j : ℕ} (hN : 0 < N)
    (hp : 1 ≤ p) (hj : j ≤ p) :
    normalization N p * Real.sqrt N ^ (p - j) * Real.sqrt N =
      (N : ℝ) ^ (1 - (j : ℝ) / 2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [normalization, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hNr.le, ← Real.rpow_add hNr, ← Real.rpow_add hNr]
  congr 1
  rw [Nat.cast_sub hj, Nat.cast_sub hp]
  push_cast
  ring

/-- Expected supremum envelope at the sharp dimension and degree scales,
proved under the genuine original product tensor law. -/
theorem expected_pureJetEnvelope_le {N p j : ℕ} (hN : 0 < N)
    (hp : 1 ≤ p) (hj : j ≤ p) :
    (∫ J, pureJetEnvelope N p j J ∂disorderLaw N p) ≤
      2 * ((j : ℝ) + 2) * (p : ℝ) ^ j * Real.sqrt p *
        (N : ℝ) ^ (1 - (j : ℝ) / 2) := by
  have h := expected_pureJetEnvelope_le_normalized (j := j) hN hp
  have he : normalization N p * Real.sqrt N ^ (p - j) *
      (2 * ((j : ℝ) + 2) * (p : ℝ) ^ j * Real.sqrt p * Real.sqrt N) =
      2 * ((j : ℝ) + 2) * (p : ℝ) ^ j * Real.sqrt p *
        (normalization N p * Real.sqrt N ^ (p - j) * Real.sqrt N) := by ring
  rwa [he, physical_normalization_identity hN hp hj] at h

/-- One constant works for all orders needed by a twice continuously
differentiable infinite mixture. -/
theorem expected_pureJetEnvelope_le_eight {N p j : ℕ} (hN : 0 < N)
    (hp : 2 ≤ p) (hj : j ≤ 2) :
    (∫ J, pureJetEnvelope N p j J ∂disorderLaw N p) ≤
      8 * (p : ℝ) ^ j * Real.sqrt p * (N : ℝ) ^ (1 - (j : ℝ) / 2) := by
  have h := expected_pureJetEnvelope_le hN (by omega : 1 ≤ p) (hj.trans hp)
  apply h.trans
  gcongr
  have hjr : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  linarith

/-- Uniform in the three low jet orders, in precisely the manuscript's
five-halves moment scale. -/
theorem expected_pureJetEnvelope_le_five_halves {N p j : ℕ} (hN : 0 < N)
    (hp : 2 ≤ p) (hj : j ≤ 2) :
    (∫ J, pureJetEnvelope N p j J ∂disorderLaw N p) ≤
      8 * (N : ℝ) * (p : ℝ) ^ (5 / 2 : ℝ) := by
  have h := expected_pureJetEnvelope_le_eight hN hp hj
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdim : (N : ℝ) ^ (1 - (j : ℝ) / 2) ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (show 1 - (j : ℝ) / 2 ≤ 1 by have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hdeg : (p : ℝ) ^ j ≤ (p : ℝ) ^ 2 := pow_le_pow_right₀ hp1 hj
  have he : (p : ℝ) ^ 2 * Real.sqrt p = (p : ℝ) ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    congr 1
    norm_num
  apply h.trans
  calc
    _ ≤ 8 * (p : ℝ) ^ 2 * Real.sqrt p * N := by gcongr
    _ = _ := by rw [show 8 * (p : ℝ) ^ 2 * Real.sqrt p * N =
      8 * (N : ℝ) * ((p : ℝ) ^ 2 * Real.sqrt p) by ring, he]

end
end SlowEquilibration.PureTensorJetBounds
