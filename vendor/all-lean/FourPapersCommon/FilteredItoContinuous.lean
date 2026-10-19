module

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
public import FourPapersCommon.FilteredItoProcess
public import StochasticCalculus.ItoFormulaGeneral

public section

/-! Full-filtration continuous versions and Doob estimates. Adapted from
Ezzeri Esa's Apache-2.0-licensed ItoMaximal, ItoFormulaGeneral and elementary
representative proofs. The actual full-filtration integration operator is
used throughout, with no reduction to an individual coordinate filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Filter Set Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace FourPapersCommon.FilteredBrownian
variable {W : Type*} [MeasurableSpace W] {P : Measure W}
  [IsProbabilityMeasure P] {B : ℝ≥0 → W → ℝ}
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
set_option maxHeartbeats 3000000
theorem naturalItoProcessRepresentative_elementaryPredictable_ae_eq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (s : ℝ≥0) :
    naturalItoProcessRepresentative hB hsm hfiltered
        (elementaryPredictable 𝓕 a b Z) s =ᵐ[P]
      fun ω => (Z : W → ℝ) ω *
        (B (min s b) ω - B (min s a) ω) := by
  let U := elementaryPredictable 𝓕 a b Z
  have hrep := naturalItoProcess_ae_eq_representative hB hsm hfiltered U s
  apply hrep.symm.trans
  by_cases hsa : s ≤ a
  · have hsb : s ≤ b := hsa.trans hab
    have hU0 : predictableTimeRestrict 𝓕 s U = 0 := by
      rw [predictableTimeRestrict_elementaryPredictable]
      apply elementaryPredictable_eq_zero_of_le
      simpa [min_eq_right hsb] using hsa
    have hproc0 : naturalItoProcess hB hsm hfiltered U s = 0 := by
      rw [naturalItoProcess, hU0, map_zero]
    rw [hproc0]
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hzero
    rw [hzero]
    simp [min_eq_left hsa, min_eq_left hsb]
  · have has : a ≤ s := le_of_not_ge hsa
    have hamin : a ≤ b ⊓ s := le_min hab has
    rw [naturalItoProcess, predictableTimeRestrict_elementaryPredictable,
      naturalItoIntegral_elementaryPredictable hB hsm hfiltered hamin]
    filter_upwards [coeFn_elementaryBrownianValue hB hsm hfiltered hamin Z]
      with ω hω
    rw [hω]
    simp only [min_comm s b, min_eq_right has]


theorem naturalItoProcess_elementaryFinsuppToPredictable [SFinite P]
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ)
    (s : ℝ≥0) :
    naturalItoProcess hB hsm hfiltered
        (elementaryFinsuppToPredictable 𝓕 P v) s =
      ∑ x ∈ v.support, v x • naturalItoProcess hB hsm hfiltered
        (elementaryPredictableGenerator 𝓕 P x) s := by
  unfold naturalItoProcess elementaryFinsuppToPredictable
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  change (naturalItoIntegral hB hsm hfiltered)
      ((predictableTimeRestrictCLM 𝓕 s)
        (∑ x ∈ v.support, v x •
          elementaryPredictableGenerator 𝓕 P x)) = _
  rw [map_sum, map_sum]
  simp only [map_smul, predictableTimeRestrictCLM_apply]

/-- The natural Itô representative of a formal finite combination is the
weighted sum of coefficients times stopped Brownian increments, almost
surely at each time. -/
theorem naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ)
    (s : ℝ≥0) :
    naturalItoProcessRepresentative hB hsm hfiltered
        (elementaryFinsuppToPredictable 𝓕 P v) s =ᵐ[P]
      fun ω => ∑ x ∈ v.support, v x * (x.2.2 : W → ℝ) ω *
        (B (min s x.2.1.1) ω - B (min s x.1) ω) := by
  let U := elementaryFinsuppToPredictable 𝓕 P v
  have hrep := naturalItoProcess_ae_eq_representative hB hsm hfiltered U s
  apply hrep.symm.trans
  rw [naturalItoProcess_elementaryFinsuppToPredictable hB hsm hfiltered v s]
  have hsum := Lp.coeFn_fun_finsetSum v.support
    (fun x => v x • naturalItoProcess hB hsm hfiltered
      (elementaryPredictableGenerator 𝓕 P x) s)
  have hterm : ∀ x ∈ v.support,
      (((v x) • naturalItoProcess hB hsm hfiltered
        (elementaryPredictableGenerator 𝓕 P x) s :
          RandomL2 P) : W → ℝ) =ᵐ[P]
        fun ω => v x * (x.2.2 : W → ℝ) ω *
          (B (min s x.2.1.1) ω - B (min s x.1) ω) := by
    intro x _hx
    have hvalue := naturalItoProcess_ae_eq_representative hB hsm hfiltered
      (elementaryPredictableGenerator 𝓕 P x) s
    have hblock :=
      naturalItoProcessRepresentative_elementaryPredictable_ae_eq
        hB hsm hfiltered x.2.1.2 x.2.2 s
    filter_upwards [Lp.coeFn_smul (v x)
        (naturalItoProcess hB hsm hfiltered
          (elementaryPredictableGenerator 𝓕 P x) s),
      hvalue, hblock] with ω hsmul hval hblk
    rw [hsmul]
    change v x * (naturalItoProcess hB hsm hfiltered
      (elementaryPredictableGenerator 𝓕 P x) s :
        W → ℝ) ω = _
    rw [hval]
    have hblk' := hblk
    change naturalItoProcessRepresentative hB hsm hfiltered
      (elementaryPredictableGenerator 𝓕 P x) s ω =
        (x.2.2 : W → ℝ) ω *
          (B (min s x.2.1.1) ω - B (min s x.1) ω) at hblk'
    rw [hblk']
    ring
  filter_upwards [hsum, v.support.eventually_all.mpr hterm] with ω hsumω htermω
  rw [hsumω]
  apply Finset.sum_congr rfl
  intro x hx
  exact htermω x hx


theorem naturalItoProcessRepresentative_sub_ae
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U V : PredictableProcessL2 𝓕 P) (s : ℝ≥0) :
    (fun ω => naturalItoProcessRepresentative hB hsm hfiltered U s ω -
        naturalItoProcessRepresentative hB hsm hfiltered V s ω) =ᵐ[P]
      naturalItoProcessRepresentative hB hsm hfiltered (U - V) s := by
  have hU := naturalItoProcess_ae_eq_representative hB hsm hfiltered U s
  have hV := naturalItoProcess_ae_eq_representative hB hsm hfiltered V s
  have hD := naturalItoProcess_ae_eq_representative hB hsm hfiltered (U - V) s
  have hlin : naturalItoProcess hB hsm hfiltered (U - V) s =
      naturalItoProcess hB hsm hfiltered U s -
        naturalItoProcess hB hsm hfiltered V s := by
    unfold naturalItoProcess
    rw [predictableTimeRestrict_sub, map_sub]
  have hcoe := Lp.coeFn_sub (naturalItoProcess hB hsm hfiltered U s)
    (naturalItoProcess hB hsm hfiltered V s)
  filter_upwards [hU, hV, hD, hcoe] with ω hUω hVω hDω hcoeω
  change (naturalItoProcess hB hsm hfiltered U s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm hfiltered U s ω at hUω
  change (naturalItoProcess hB hsm hfiltered V s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm hfiltered V s ω at hVω
  change (naturalItoProcess hB hsm hfiltered (U - V) s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm hfiltered (U - V) s ω at hDω
  rw [← hUω, ← hVω, ← hDω, hlin, hcoeω]
  rfl


theorem martingale_naturalItoProcessRepresentative_uniformPartition
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) (n : ℕ) :
    Martingale
      (fun k => naturalItoProcessRepresentative hB hsm hfiltered U
        (uniformPartitionTime t n k))
      (uniformPartitionFiltration 𝓕 t n) P := by
  exact martingale_comp_monotone
    (martingale_naturalItoProcessRepresentative hB hsm hfiltered U)
    (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)

/-- Every fixed-time value of the selected representative of a natural Itô
process has an integrable square. -/
theorem integrable_sq_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) :
    Integrable (fun ω =>
      (naturalItoProcessRepresentative hB hsm hfiltered U t ω) ^ 2) P := by
  let It := naturalItoProcess hB hsm hfiltered U t
  have hbase : Integrable (fun ω => (((It : RandomL2 P) : W → ℝ) ω) ^ 2) P :=
    (Lp.memLp It).integrable_sq
  apply hbase.congr
  filter_upwards [naturalItoProcess_ae_eq_representative hB hsm hfiltered U t]
    with ω ht
  change ((It : W → ℝ) ω) =
    naturalItoProcessRepresentative hB hsm hfiltered U t ω at ht
  rw [ht]

/-- Representative-level fixed-time Itô isometry. -/
theorem integral_sq_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) :
    ∫ ω, (naturalItoProcessRepresentative hB hsm hfiltered U t ω) ^ 2 ∂P =
      ‖naturalItoProcess hB hsm hfiltered U t‖ ^ 2 := by
  calc
    ∫ ω, (naturalItoProcessRepresentative hB hsm hfiltered U t ω) ^ 2 ∂P =
        ∫ ω, ((naturalItoProcess hB hsm hfiltered U t : RandomL2 P) : W → ℝ) ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [naturalItoProcess_ae_eq_representative hB hsm hfiltered U t]
        with ω ht
      rw [ht]
    _ = inner ℝ (naturalItoProcess hB hsm hfiltered U t)
        (naturalItoProcess hB hsm hfiltered U t) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with ω
      simp [pow_two]
    _ = ‖naturalItoProcess hB hsm hfiltered U t‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Doob's `L²` estimate for the selected natural Itô process on every
uniform grid.  The right side is independent of the mesh size; this is the
key estimate needed for the elementary-density continuous-modification
argument. -/
theorem naturalItoProcessRepresentative_uniformPartition_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (ε : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ε * P {ω |
        (ε : ℝ) ≤ (Finset.range (n + 2)).sup'
          Finset.nonempty_range_add_one
          (fun k =>
            (naturalItoProcessRepresentative hB hsm hfiltered U
              (uniformPartitionTime t (n + 1) k) ω) ^ 2)} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let M : ℕ → W → ℝ := fun k =>
    naturalItoProcessRepresentative hB hsm hfiltered U
      (uniformPartitionTime t (n + 1) k)
  have hM : Martingale M
      (uniformPartitionFiltration 𝓕 t (n + 1)) P := by
    simpa only [M] using
      martingale_naturalItoProcessRepresentative_uniformPartition
        hB hsm hfiltered U t (n + 1)
  have hM2 : ∀ k, Integrable (fun ω => (M k ω) ^ 2) P := by
    intro k
    simpa only [M] using integrable_sq_naturalItoProcessRepresentative
      hB hsm hfiltered U (uniformPartitionTime t (n + 1) k)
  have hDoob := martingale_maximal_sq_ineq hM hM2 ε (n + 1)
  have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
    rw [uniformPartitionTime]
    exact mul_div_cancel_right₀ t hn
  calc
    ε * P {ω |
          (ε : ℝ) ≤ (Finset.range (n + 2)).sup'
            Finset.nonempty_range_add_one
            (fun k =>
              (naturalItoProcessRepresentative hB hsm hfiltered U
                (uniformPartitionTime t (n + 1) k) ω) ^ 2)} ≤
        ENNReal.ofReal (∫ ω, (M (n + 1) ω) ^ 2 ∂P) := by
      simpa only [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hDoob
    _ = ENNReal.ofReal
        (‖naturalItoProcess hB hsm hfiltered U t‖ ^ 2) := by
      rw [show M (n + 1) = naturalItoProcessRepresentative hB hsm hfiltered U t by
        funext ω
        simp only [M, htop]]
      rw [integral_sq_naturalItoProcessRepresentative]
    _ ≤ ENNReal.ofReal (‖U‖ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
        (norm_naturalItoProcess_le hB hsm hfiltered U t)

/-- The mesh-independent maximal estimate on the nested dyadic grids. -/
theorem naturalItoProcessRepresentative_dyadicPartition_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (ε : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ε * P {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
        (naturalItoProcessRepresentative hB hsm hfiltered U) t n ω} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hdenom : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hone
  have hrange : 2 ^ n - 1 + 2 = 2 ^ n + 1 := by omega
  simpa only [dyadicPartitionSqMax, hdenom, hrange] using
    naturalItoProcessRepresentative_uniformPartition_maximal_sq_ineq
      hB hsm hfiltered U ε t (2 ^ n - 1)

/-- Doob's estimate on the union of all nested dyadic-grid events.  This is
the countable event that becomes a compact-time supremum event for a
continuous representative. -/
theorem naturalItoProcessRepresentative_dyadicPartition_maximal_sq_iUnion
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P (⋃ n : ℕ, {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
        (naturalItoProcessRepresentative hB hsm hfiltered U) t n ω}) ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let S : ℕ → Set W := fun n => {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
    (naturalItoProcessRepresentative hB hsm hfiltered U) t n ω}
  have hS : Monotone S := by
    intro n m hnm ω hω
    exact hω.trans (monotone_dyadicPartitionSqMax
      (naturalItoProcessRepresentative hB hsm hfiltered U) t ω hnm)
  rw [show (⋃ n : ℕ, {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
      (naturalItoProcessRepresentative hB hsm hfiltered U) t n ω}) =
      ⋃ n, S n by rfl]
  rw [hS.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  exact naturalItoProcessRepresentative_dyadicPartition_maximal_sq_ineq
    hB hsm hfiltered U ε t n


theorem IsContinuousProcessModification.naturalIto_compact_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered U) Y P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P {omega | ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let R : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB hsm hfiltered U
  let A : Set W :=
    {omega | ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2}
  let D : Set W :=
    ⋃ n : ℕ, {omega | (ε : ℝ) ≤ dyadicPartitionSqMax R t n omega}
  have hdyadic : ∀ᵐ omega ∂P, ∀ n : ℕ,
      dyadicPartitionSqMax Y t n omega =
        dyadicPartitionSqMax R t n omega := by
    apply ae_all_iff.mpr
    intro n
    exact (dyadicPartitionSqMax_congr_ae hmod.fixedTime_ae_eq t n).symm
  have hAD : A ≤ᵐ[P] D := by
    filter_upwards [hmod.continuous_paths, hdyadic] with omega hcontinuous heq
    intro homega
    change ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2 at homega
    obtain ⟨s, hst, hs⟩ := homega
    obtain ⟨n, hn⟩ := exists_lt_dyadicPartitionSqMax_of_continuous
      Y t omega hcontinuous hst hs
    simp only [D, Set.mem_iUnion]
    refine ⟨n, ?_⟩
    change (ε : ℝ) ≤ dyadicPartitionSqMax R t n omega
    rw [← heq n]
    exact hn.le
  change (ε : ℝ≥0∞) * P A ≤ ENNReal.ofReal (‖U‖ ^ 2)
  calc
    (ε : ℝ≥0∞) * P A ≤ (ε : ℝ≥0∞) * P D :=
      mul_le_mul_of_nonneg_left (measure_mono_ae hAD) bot_le
    _ ≤ ENNReal.ofReal (‖U‖ ^ 2) := by
      exact naturalItoProcessRepresentative_dyadicPartition_maximal_sq_iUnion
        hB hsm hfiltered U ε t

/-- The difference of continuous modifications of two natural Itô processes
is a continuous modification of the natural Itô process of the integrand
difference.  Representative linearity is used only at fixed times, where it
is valid almost everywhere. -/
theorem naturalItoContinuousModification_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U V : PredictableProcessL2 𝓕 P)
    {YU YV : ℝ≥0 → W → ℝ}
    (hU : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered U) YU P)
    (hV : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered V) YV P) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered (U - V))
      (fun s omega => YU s omega - YV s omega) P := by
  constructor
  · intro s
    filter_upwards [naturalItoProcessRepresentative_sub_ae hB hsm hfiltered U V s,
      hU.fixedTime_ae_eq s, hV.fixedTime_ae_eq s]
      with omega hsub hYU hYV
    rw [← hsub, hYU, hYV]
  · filter_upwards [hU.continuous_paths, hV.continuous_paths]
      with omega hYU hYV
    exact hYU.sub hYV

/-- Compact-time Doob estimate for the difference of any two continuous
natural-Itô representatives.  This is the uniform-Cauchy estimate consumed
by the predictable-`L²` density construction. -/
theorem naturalItoContinuousModification_sub_compact_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U V : PredictableProcessL2 𝓕 P)
    {YU YV : ℝ≥0 → W → ℝ}
    (hU : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered U) YU P)
    (hV : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered V) YV P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P {omega | ∃ s : ℝ≥0, s ≤ t ∧
        (ε : ℝ) < (YU s omega - YV s omega) ^ 2} ≤
      ENNReal.ofReal (‖U - V‖ ^ 2) := by
  have hmod := naturalItoContinuousModification_sub hB hsm hfiltered U V hU hV
  exact IsContinuousProcessModification.naturalIto_compact_maximal_sq_ineq
    hB hsm hfiltered (U - V) hmod ε t

/-- Borel--Cantelli consequence of the compact maximal estimate.  If the
normalized squared `L²` increments of a sequence of integrands are summable,
then the corresponding continuous representatives eventually have uniformly
small successive increments on `[0,t]`, almost surely. -/
theorem naturalItoContinuousModifications_eventually_uniform_step
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : ℕ → PredictableProcessL2 𝓕 P)
    (Y : ℕ → ℝ≥0 → W → ℝ)
    (hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered (U n)) (Y n) P)
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (hsum : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞)
    (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in Filter.atTop, ∀ s : ℝ≥0, s ≤ t →
      (Y (n + 1) s omega - Y n s omega) ^ 2 ≤ (δ n : ℝ) := by
  let A : ℕ → Set W := fun n =>
    {omega | ∃ s : ℝ≥0, s ≤ t ∧
      (δ n : ℝ) < (Y (n + 1) s omega - Y n s omega) ^ 2}
  have hmeasure : ∀ n,
      P (A n) ≤
        ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞) := by
    intro n
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.coe_ne_zero.mpr (ne_of_gt (hδ n))))
      (Or.inl ENNReal.coe_ne_top)).2
    rw [mul_comm]
    exact naturalItoContinuousModification_sub_compact_maximal_sq_ineq
      hB hsm hfiltered (U (n + 1)) (U n) (hmod (n + 1)) (hmod n) (δ n) t
  have hsumMeasure : (∑' n : ℕ, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hmeasure)
  have hBC := ae_eventually_notMem hsumMeasure
  filter_upwards [hBC] with omega homega
  filter_upwards [homega] with n hn
  intro s hst
  by_contra hle
  exact hn ⟨s, hst, lt_of_not_ge hle⟩

/-- Pointwise canonical limit of a sequence of candidate process
representatives.  The fallback branch is irrelevant on the almost-everywhere
set where the sequence is Cauchy. -/
@[expose] noncomputable def continuousModificationSequenceLimit
    (Y : ℕ → ℝ≥0 → W → ℝ) : ℝ≥0 → W → ℝ :=
  fun s omega => completeCauchySeqLimit (fun n => Y n s omega)

/-- Closure of continuous natural-Itô modifications under a sufficiently
fast predictable-`L²` limit.  The two summability hypotheses are exactly the
probabilistic Borel--Cantelli bound and the deterministic uniform-Cauchy
bound, respectively. -/
theorem continuousModification_naturalItoProcess_of_fast_tendsto
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (V : PredictableProcessL2 𝓕 P)
    (U : ℕ → PredictableProcessL2 𝓕 P)
    (Y : ℕ → ℝ≥0 → W → ℝ)
    (hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered (U n)) (Y n) P)
    (hUV : Filter.Tendsto U Filter.atTop (nhds V))
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (hsumProbability : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞)
    (hsumUniform : Summable (fun n => Real.sqrt (δ n : ℝ))) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm hfiltered V)
      (continuousModificationSequenceLimit Y) P := by
  have hcontinuous : ∀ᵐ omega ∂P, ∀ n : ℕ,
      Continuous (fun s => Y n s omega) := by
    apply ae_all_iff.mpr
    intro n
    exact (hmod n).continuous_paths
  have hsteps : ∀ᵐ omega ∂P, ∀ k : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop, ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) →
        (Y (n + 1) s omega - Y n s omega) ^ 2 ≤ (δ n : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    exact naturalItoContinuousModifications_eventually_uniform_step
      hB hsm hfiltered U Y hmod δ hδ hsumProbability k
  have huniform : ∀ᵐ omega ∂P, ∀ k : ℕ,
      UniformCauchySeqOn (fun n s => Y n s omega) Filter.atTop
        (Set.Iic (k : ℝ≥0)) := by
    filter_upwards [hsteps] with omega homega
    intro k
    apply uniformCauchySeqOn_of_eventually_dist_le_of_summable
      (fun n s => Y n s omega) (Set.Iic (k : ℝ≥0))
      (fun n => Real.sqrt (δ n : ℝ))
      (fun n => Real.sqrt_nonneg _) hsumUniform
    filter_upwards [homega k] with n hn
    intro s hs
    have hsqrt := Real.sqrt_le_sqrt (hn s hs)
    simpa only [Real.dist_eq, Real.sqrt_sq_eq_abs, abs_sub_comm] using hsqrt
  constructor
  · intro s
    obtain ⟨k, hsk⟩ : ∃ k : ℕ, s ≤ (k : ℝ≥0) := exists_nat_ge s
    have hpointwise : ∀ᵐ omega ∂P,
        Filter.Tendsto (fun n => Y n s omega) Filter.atTop
          (nhds (continuousModificationSequenceLimit Y s omega)) := by
      filter_upwards [huniform] with omega homega
      unfold continuousModificationSequenceLimit
      exact tendsto_completeCauchySeqLimit ((homega k).cauchySeq hsk)
    have hYmeas : ∀ n, AEStronglyMeasurable (Y n s) P := by
      intro n
      have hrepmeas : AEStronglyMeasurable
          (naturalItoProcessRepresentative hB hsm hfiltered (U n) s) P :=
        AEStronglyMeasurable.mono (𝓕.le s)
          (stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm hfiltered (U n) s).aestronglyMeasurable
      exact hrepmeas.congr ((hmod n).fixedTime_ae_eq s)
    have hrestrict : Filter.Tendsto
        (fun n => predictableTimeRestrict 𝓕 s (U n))
        Filter.atTop
        (nhds (predictableTimeRestrict 𝓕 s V)) := by
      change Filter.Tendsto
        ((predictableTimeRestrictCLM 𝓕 s) ∘ U)
        Filter.atTop
        (nhds (predictableTimeRestrict 𝓕 s V))
      exact ((predictableTimeRestrictCLM
        𝓕 s).continuous.tendsto V).comp hUV
    have hLp : Filter.Tendsto
        (fun n => naturalItoProcess hB hsm hfiltered (U n) s)
        Filter.atTop (nhds (naturalItoProcess hB hsm hfiltered V s)) := by
      change Filter.Tendsto
        ((naturalItoIntegral hB hsm hfiltered) ∘
          fun n => predictableTimeRestrict 𝓕 s (U n))
        Filter.atTop
        (nhds (naturalItoProcess hB hsm hfiltered V s))
      exact ((naturalItoIntegral hB hsm hfiltered).continuous.tendsto
        (predictableTimeRestrict 𝓕 s V)).comp hrestrict
    have htoTarget : TendstoInMeasure P (fun n => Y n s) Filter.atTop
        (naturalItoProcessRepresentative hB hsm hfiltered V s) := by
      have hraw := tendstoInMeasure_of_tendsto_Lp hLp
      apply TendstoInMeasure.congr_right
        (naturalItoProcess_ae_eq_representative hB hsm hfiltered V s)
      apply TendstoInMeasure.congr_left _ hraw
      intro n
      exact (naturalItoProcess_ae_eq_representative hB hsm hfiltered (U n) s).trans
        ((hmod n).fixedTime_ae_eq s)
    have htoLimit : TendstoInMeasure P (fun n => Y n s) Filter.atTop
        (continuousModificationSequenceLimit Y s) :=
      tendstoInMeasure_of_tendsto_ae hYmeas hpointwise
    exact tendstoInMeasure_ae_unique htoTarget htoLimit
  · filter_upwards [hcontinuous, huniform] with omega hcont huc
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨k, hsk⟩ : ∃ k : ℕ, s < (k : ℝ≥0) := exists_nat_gt s
    have hlimitContinuous : ContinuousOn
        (continuousModificationSequenceLimit Y · omega)
        (Set.Iic (k : ℝ≥0)) := by
      unfold continuousModificationSequenceLimit
      exact continuousOn_completeCauchySeqLimit
        (fun n s => Y n s omega) (Set.Iic (k : ℝ≥0)) (huc k)
          (fun n => (hcont n).continuousOn)
    exact hlimitContinuous.continuousAt (Iic_mem_nhds hsk)

/-- The explicit continuous Brownian-block representative of the natural Itô
process associated with a finite elementary predictable integrand. -/
@[expose] noncomputable def elementaryFinsuppItoContinuousRepresentative
    (B : ℝ≥0 → W → ℝ) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    ℝ≥0 → W → ℝ :=
  fun s omega => ∑ x ∈ v.support,
    v x * (x.2.2 : W → ℝ) omega *
      (B (min s x.2.1.1) omega - B (min s x.1) omega)

/-- On the finite elementary predictable layer, the selected natural Itô
representative has an explicit continuous modification. -/
theorem elementaryFinsuppItoContinuousModification
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered
        (elementaryFinsuppToPredictable
          𝓕 P v))
      (elementaryFinsuppItoContinuousRepresentative B hsm hfiltered v) P := by
  constructor
  · intro s
    change naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered
        (elementaryFinsuppToPredictable
          𝓕 P v) s =ᵐ[P]
      (fun omega => ∑ x ∈ v.support, v x * (x.2.2 : W → ℝ) omega *
        (B (min s x.2.1.1) omega - B (min s x.1) omega))
    exact naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
      hB.toIsPreBrownianReal hsm hfiltered v s
  · filter_upwards [hB.cont] with omega hBcontinuous
    unfold elementaryFinsuppItoContinuousRepresentative
    apply continuous_finsetSum
    intro x _hx
    exact continuous_const.mul
      ((hBcontinuous.comp (continuous_id.min continuous_const)).sub
        (hBcontinuous.comp (continuous_id.min continuous_const)))

/-- Quantitative version of elementary density: the approximation rate may
be prescribed arbitrarily, as long as every requested radius is positive.
This is the form used to choose a Borel--Cantelli-fast sequence. -/
theorem exists_elementaryFinsupp_continuousModifications_dist_lt
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∃ v : ℕ →
        (ElementaryPredictableIndex 𝓕 P →₀ ℝ),
      (∀ n, dist U
        (elementaryFinsuppToPredictable
          𝓕 P (v n)) < r n) ∧
      ∀ n, IsContinuousProcessModification
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered
          (elementaryFinsuppToPredictable
            𝓕 P (v n)))
        (elementaryFinsuppItoContinuousRepresentative B hsm hfiltered (v n)) P := by
  have hdense := denseRange_elementaryFinsuppToPredictable (P := P)
    𝓕
  choose v hv using fun n => hdense.exists_dist_lt U (hr n)
  refine ⟨v, hv, ?_⟩
  intro n
  exact elementaryFinsuppItoContinuousModification hB hsm hfiltered (v n)

/-- Every natural Itô process has a continuous modification.  Choose
elementary predictable integrands within `8⁻ⁿ` of the target.  Their
successive squared `L²` distances are dominated by `4 · 64⁻ⁿ`; with
thresholds `4⁻ⁿ`, both series required by the fast-limit closure theorem
are geometric. -/
theorem exists_continuousModification_naturalItoProcess
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (V : PredictableProcessL2 𝓕 P) :
    ∃ Y : ℝ≥0 → W → ℝ, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered V) Y P := by
  let r : ℕ → ℝ := fun n => (1 / 8 : ℝ) ^ n
  obtain ⟨v, hv, hvmod⟩ :=
    exists_elementaryFinsupp_continuousModifications_dist_lt
      hB hsm hfiltered V r (by intro n; simp only [r]; positivity)
  let U : ℕ → PredictableProcessL2 𝓕 P :=
    fun n => elementaryFinsuppToPredictable
      𝓕 P (v n)
  let Y : ℕ → ℝ≥0 → W → ℝ :=
    fun n => elementaryFinsuppItoContinuousRepresentative B hsm hfiltered (v n)
  let δ : ℕ → ℝ≥0 := fun n => (1 / 4 : ℝ≥0) ^ n
  have hdist : ∀ n, dist V (U n) < (1 / 8 : ℝ) ^ n := by
    intro n
    simpa only [U, r] using hv n
  have hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered (U n))
      (Y n) P := by
    intro n
    simpa only [U, Y] using hvmod n
  have hUV : Filter.Tendsto U Filter.atTop (nhds V) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hpow : Filter.Tendsto (fun n : ℕ => (1 / 8 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hpow ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hr : (1 / 8 : ℝ) ^ n < ε := by
      have hrabs := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (pow_nonneg (by norm_num) n)] at hrabs
      exact hrabs
    have hn := hdist n
    rw [dist_comm] at hn
    exact hn.trans hr
  have hδ : ∀ n, 0 < δ n := by
    intro n
    simp only [δ]
    positivity
  have hsq : ∀ n, ‖U (n + 1) - U n‖ ^ 2 ≤
      4 * (1 / 64 : ℝ) ^ n := by
    intro n
    have hstep : ‖U (n + 1) - U n‖ < 2 * (1 / 8 : ℝ) ^ n := by
      calc
        ‖U (n + 1) - U n‖ = dist (U (n + 1)) (U n) :=
          (dist_eq_norm _ _).symm
        _ ≤ dist (U (n + 1)) V + dist V (U n) := dist_triangle _ _ _
        _ < (1 / 8 : ℝ) ^ (n + 1) + (1 / 8 : ℝ) ^ n :=
          add_lt_add (by simpa only [dist_comm] using hdist (n + 1))
            (hdist n)
        _ ≤ 2 * (1 / 8 : ℝ) ^ n := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) n]
    have hsq' : ‖U (n + 1) - U n‖ ^ 2 ≤
        (2 * (1 / 8 : ℝ) ^ n) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hstep.le
    calc
      ‖U (n + 1) - U n‖ ^ 2 ≤ (2 * (1 / 8 : ℝ) ^ n) ^ 2 := hsq'
      _ = 4 * (1 / 64 : ℝ) ^ n := by
        have hp : ((1 / 8 : ℝ) ^ n) ^ 2 = (1 / 64 : ℝ) ^ n := by
          rw [show (1 / 64 : ℝ) = (1 / 8 : ℝ) ^ 2 by norm_num]
          simp only [← pow_mul, Nat.mul_comm]
        rw [mul_pow, hp]
        norm_num
  have hnormalized : ∀ n,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞) ≤
        4 * (1 / 16 : ℝ≥0∞) ^ n := by
    intro n
    change ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) /
        ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) ≤
      4 * (1 / 16 : ℝ≥0∞) ^ n
    calc
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) /
            ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) ≤
          ENNReal.ofReal (4 * (1 / 64 : ℝ) ^ n) /
            ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact hsq n
      _ = 4 * (1 / 16 : ℝ≥0∞) ^ n := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.coe_pow]
        have hofReal : ENNReal.ofReal (1 / 64 : ℝ) =
            (1 / 64 : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)]
          norm_num
        rw [hofReal]
        norm_num only [ENNReal.ofReal_ofNat, ENNReal.coe_div,
          ENNReal.coe_one, ENNReal.coe_ofNat]
        rw [mul_div_assoc]
        congr 1
        simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow, ← mul_pow]
        congr 1
        simp only [mul_one, inv_inv]
        change ((4 : ℝ≥0) : ℝ≥0∞) *
            (((64 : ℝ≥0) : ℝ≥0∞))⁻¹ =
          (((16 : ℝ≥0) : ℝ≥0∞))⁻¹
        rw [← ENNReal.coe_inv (by norm_num : (64 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_inv (by norm_num : (16 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_mul]
        norm_num
  have hsumProbability : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (b := ∑' n : ℕ, 4 * (1 / 16 : ℝ≥0∞) ^ n)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.inv_ne_top.mpr
          (ne_of_gt (tsub_pos_iff_lt.mpr
            (by norm_num : (1 / 16 : ℝ≥0∞) < 1)))
    · exact ENNReal.tsum_le_tsum hnormalized
  have hsumUniform : Summable (fun n => Real.sqrt (δ n : ℝ)) := by
    change Summable (fun n : ℕ => Real.sqrt ((1 / 4 : ℝ) ^ n))
    apply (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
      (by positivity) (by norm_num)).congr
    intro n
    have hp : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num]
      simp only [← pow_mul, Nat.mul_comm]
    rw [hp, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  exact ⟨continuousModificationSequenceLimit Y,
    continuousModification_naturalItoProcess_of_fast_tendsto
      hB.toIsPreBrownianReal hsm hfiltered V U Y hmod hUV δ hδ
        hsumProbability hsumUniform⟩


end FourPapersCommon.FilteredBrownian
