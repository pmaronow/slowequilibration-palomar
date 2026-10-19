-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGEnsemble
public import SlowEquilibration.DirectingPhysicalStarDecay
public import Mathlib.Tactic

/-! Origin removal from one genuine covariance GG identity. The replica
laws are the actual finite independent products of a random directing
kernel. Odd covariance tests are allowed: only an upper bound is used in
the zero-star recurrence, and no positivity of individual overlaps is
assumed. This is the last step of manuscript Theorem 6.3. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.DirectingPhysical

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open GaussianReplicaKernel GaussianGGEnsemble

set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

def zeroStar (ψ : ℝ → ℝ) (m : ℕ) : Set (Fin (m + 1) → H) :=
  {σ | ∀ j : Fin m, ψ (inner ℝ (σ 0) (σ j.succ)) = 0}

def zeroStarIndicator (ψ : ℝ → ℝ) (m : ℕ) : (Fin (m + 1) → H) → ℝ :=
  (zeroStar ψ m).indicator (fun _ => 1)

def zeroStarMass (d : Measure Ω) (G : Kernel Ω H) (ψ : ℝ → ℝ) (m : ℕ) : ℝ :=
  (law d G (m + 1)).real (zeroStar ψ m)

/-- Literal finite overlap array of a directing sample. The diagonal
is one, as in the Dovbysh--Sudakov array, independently of vector norms. -/
def finiteOverlapArray (n : ℕ) (σ : Fin n → H) : Fin n × Fin n → ℝ :=
  fun ij => if ij.1 = ij.2 then 1 else inner ℝ (σ ij.1) (σ ij.2)

def arrayZeroStar (ψ : ℝ → ℝ) (m : ℕ) : Set (Fin (m + 1) × Fin (m + 1) → ℝ) :=
  {r | ∀ j : Fin m, ψ (r (0, j.succ)) = 0}

def arrayZeroStarIndicator (ψ : ℝ → ℝ) (m : ℕ) :
    (Fin (m + 1) × Fin (m + 1) → ℝ) → ℝ :=
  (arrayZeroStar ψ m).indicator (fun _ => 1)

theorem arrayZeroStar_closed {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    IsClosed (arrayZeroStar ψ m) := by
  unfold arrayZeroStar
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_eq (hψ.comp (continuous_apply (0, j.succ))) continuous_const

theorem arrayZeroStarIndicator_measurable {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    Measurable (arrayZeroStarIndicator ψ m) :=
  measurable_const.indicator (arrayZeroStar_closed hψ m).measurableSet

theorem arrayZeroStarIndicator_bound (ψ : ℝ → ℝ) (m : ℕ)
    (r : Fin (m + 1) × Fin (m + 1) → ℝ) : |arrayZeroStarIndicator ψ m r| ≤ 1 := by
  classical
  unfold arrayZeroStarIndicator
  by_cases h : r ∈ arrayZeroStar ψ m
  · rw [indicator_of_mem h]; norm_num
  · rw [indicator_of_notMem h]; norm_num

/-- Zero-star tests depend only on overlaps, so the covariance GG
hypothesis never requires arbitrary functions of directing vectors. -/
theorem arrayZeroStarIndicator_eq (ψ : ℝ → ℝ) (m : ℕ) (σ : Fin (m + 1) → H) :
    arrayZeroStarIndicator ψ m (finiteOverlapArray (m + 1) σ) = zeroStarIndicator ψ m σ := by
  classical
  have hmem : finiteOverlapArray (m + 1) σ ∈ arrayZeroStar ψ m ↔ σ ∈ zeroStar ψ m := by
    have hne (j : Fin m) : (0 : Fin (m + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    simp [arrayZeroStar, zeroStar, finiteOverlapArray, hne]
  unfold arrayZeroStarIndicator zeroStarIndicator
  by_cases h : σ ∈ zeroStar ψ m
  · rw [indicator_of_mem h, indicator_of_mem (hmem.mpr h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mp h'))]

theorem zeroStar_closed {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    IsClosed (zeroStar (H := H) ψ m) := by
  unfold zeroStar
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_eq (hψ.comp ((continuous_apply 0).inner (continuous_apply j.succ)))
    continuous_const

theorem zeroStarIndicator_measurable {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    Measurable (zeroStarIndicator (H := H) ψ m) :=
  measurable_const.indicator (zeroStar_closed hψ m).measurableSet

theorem zeroStarIndicator_mem (ψ : ℝ → ℝ) (m : ℕ) (σ : Fin (m + 1) → H) :
    zeroStarIndicator ψ m σ ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold zeroStarIndicator
  by_cases h : σ ∈ zeroStar ψ m
  · rw [indicator_of_mem h]; norm_num
  · rw [indicator_of_notMem h]; norm_num

theorem zeroStarIndicator_integral (d : Measure Ω) (G : Kernel Ω H)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    (∫ σ, zeroStarIndicator ψ m σ ∂law d G (m + 1)) = zeroStarMass d G ψ m := by
  rw [zeroStarIndicator, integral_indicator_const 1 (zeroStar_closed hψ m).measurableSet,
    smul_eq_mul, mul_one]
  rfl

theorem zeroStarPrefix_integral (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    (∫ σ, zeroStarIndicator ψ m (initial σ) ∂law d G (m + 2)) =
      zeroStarMass d G ψ m := by
  have h := (initial_hasLaw d G (m + 1)).integral_comp
    (zeroStarIndicator_measurable hψ m).aestronglyMeasurable
  calc
    _ = ∫ σ, zeroStarIndicator ψ m σ ∂law d G (m + 1) := h
    _ = _ := zeroStarIndicator_integral d G hψ m

/-- The one covariance GG identity, on literal independent directing
replicas. Its independent term uses the true mean of the pair law. -/
def CovarianceGG (d : Measure Ω) (G : Kernel Ω H) (ψ : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∀ f : (Fin (m + 1) × Fin (m + 1) → ℝ) → ℝ,
    Measurable f → (∀ r, |f r| ≤ 1) →
    (∫ σ, f (finiteOverlapArray (m + 1) (initial σ)) * ψ (GaussianGGStarRecursion.freshOverlap m σ)
      ∂law d G (m + 2)) =
      (∫ r, ψ r ∂overlapLaw d G) / ((m : ℝ) + 1) *
        (∫ σ, f (finiteOverlapArray (m + 1) σ) ∂law d G (m + 1)) +
      (∑ j : Fin m, ∫ σ, f (finiteOverlapArray (m + 1) (initial σ)) *
        ψ (GaussianGGStarRecursion.oldOverlap m j σ)
        ∂law d G (m + 2)) / ((m : ℝ) + 1)

theorem zeroStar_old_vanishes (ψ : ℝ → ℝ) (m : ℕ) (j : Fin m)
    (σ : Fin (m + 2) → H) :
    zeroStarIndicator ψ m (initial σ) *
      ψ (GaussianGGStarRecursion.oldOverlap m j σ) = 0 := by
  classical
  by_cases h : initial σ ∈ zeroStar ψ m
  · rw [zeroStarIndicator, indicator_of_mem h]
    have hz := h j
    change ψ (inner ℝ (σ 0) (σ j.succ.castSucc)) = 0 at hz
    simpa [GaussianGGStarRecursion.oldOverlap] using hz
  · rw [zeroStarIndicator, indicator_of_notMem h, zero_mul]

/-- On the literal zero-star event the old-neighbor terms in GG vanish. -/
theorem zeroStar_fresh_identity (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hGG : CovarianceGG d G ψ) (m : ℕ) :
    (∫ σ, zeroStarIndicator ψ m (initial σ) *
      ψ (GaussianGGStarRecursion.freshOverlap m σ) ∂law d G (m + 2)) =
      (∫ r, ψ r ∂overlapLaw d G) / ((m : ℝ) + 1) * zeroStarMass d G ψ m := by
  have h := hGG m (arrayZeroStarIndicator ψ m) (arrayZeroStarIndicator_measurable hψ m)
    (arrayZeroStarIndicator_bound ψ m)
  simp_rw [arrayZeroStarIndicator_eq] at h
  simp_rw [zeroStar_old_vanishes, integral_zero] at h
  simpa only [zeroStarIndicator_integral d G hψ m, Finset.sum_const_zero,
    zero_div, add_zero] using h

/-- Pointwise signed-covariance estimate: the fresh observable vanishes
on the next zero-star event, and elsewhere needs only its upper bound. -/
theorem zeroStar_fresh_upper (ψ : ℝ → ℝ) (m : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    (σ : Fin (m + 2) → H)
    (hupper : ψ (GaussianGGStarRecursion.freshOverlap m σ) ≤ C) :
    zeroStarIndicator ψ m (initial σ) *
      ψ (GaussianGGStarRecursion.freshOverlap m σ) ≤
        C * (zeroStarIndicator ψ m (initial σ) - zeroStarIndicator ψ (m + 1) σ) := by
  classical
  have hp : σ ∈ zeroStar ψ (m + 1) ↔ initial σ ∈ zeroStar ψ m ∧
      ψ (GaussianGGStarRecursion.freshOverlap m σ) = 0 := by
    unfold zeroStar
    simp only [mem_ofPred_eq, Fin.forall_iff_castSucc]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · rintro ⟨h, hz⟩
      exact ⟨hz, h⟩
  by_cases hs : initial σ ∈ zeroStar ψ m
  · by_cases hn : σ ∈ zeroStar ψ (m + 1)
    · simp only [zeroStarIndicator, indicator_of_mem hs, indicator_of_mem hn]
      rw [(hp.mp hn).2]
      simp
    · simp only [zeroStarIndicator, indicator_of_mem hs, indicator_of_notMem hn]
      simpa using hupper
  · have hn : σ ∉ zeroStar ψ (m + 1) := fun h => hs (hp.mp h).1
    simp only [zeroStarIndicator, indicator_of_notMem hs, indicator_of_notMem hn]
    simp

/-- The true disorder-averaged mass of the origin. -/
def originMass (d : Measure Ω) (G : Kernel Ω H) : ℝ :=
  ∫ ω, (G ω).real ({0} : Set H) ∂d

theorem kernel_origin_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] :
    Integrable (fun ω => (G ω).real ({0} : Set H)) d := by
  apply Integrable.of_bound
    ((G.measurable_coe (measurableSet_singleton 0)).ennreal_toReal).aestronglyMeasurable 1
  exact .of_forall fun ω => by
    change ‖(G ω).real ({0} : Set H)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

/-- A replica at the origin forces every tested overlap in its star to
be zero. Thus the origin mass is a lower bound on each actual star mass. -/
theorem originMass_le_zeroStarMass (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψ0 : ψ 0 = 0) (m : ℕ) : originMass d G ≤ zeroStarMass d G ψ m := by
  rw [zeroStarMass, replicaLaw_real_eq_integral d G (m + 1) _
    (zeroStar_closed hψ m).measurableSet, originMass]
  have hm : Measurable (fun ω =>
      (Measure.pi (fun _ : Fin (m + 1) => G ω)).real (zeroStar ψ m)) := by
    simpa only [iid_apply, Measure.real] using
      ((iid G (m + 1)).measurable_coe (zeroStar_closed hψ m).measurableSet).ennreal_toReal
  have hi : Integrable (fun ω =>
      (Measure.pi (fun _ : Fin (m + 1) => G ω)).real (zeroStar ψ m)) d := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  apply integral_mono (kernel_origin_integrable d G) hi
  intro ω
  change (G ω).real ({0} : Set H) ≤
    (Measure.pi (fun _ : Fin (m + 1) => G ω)).real (zeroStar ψ m)
  have heval := (measurePreserving_eval (fun _ : Fin (m + 1) => G ω)
    (0 : Fin (m + 1))).hasLaw.measureReal_eq (p := fun v : H => v = 0)
      (measurableSet_singleton 0)
  change (Measure.pi (fun _ : Fin (m + 1) => G ω)).real {σ | σ 0 = 0} =
    (G ω).real ({0} : Set H) at heval
  rw [← heval]
  apply measureReal_mono ?_ (by finiteness)
  intro σ hσ j
  change σ 0 = 0 at hσ
  change ψ (inner ℝ (σ 0) (σ j.succ)) = 0
  rw [hσ, inner_zero_left, hψ0]

/-- The actual random directing kernel has no atom at zero if its one
covariance GG identity has a positive pair mean. No origin exclusion,
star decay, overlap positivity, or norm-support conclusion is assumed. -/
theorem origin_ae_zero_of_covarianceGG (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψ0 : ψ 0 = 0)
    (hball : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ≤ 1)
    {D C : ℝ} (hbound : ∀ r ∈ Icc (-1 : ℝ) 1, |ψ r| ≤ D) (hC : 0 < C)
    (hupper : ∀ᵐ r ∂overlapLaw d G, ψ r ≤ C)
    (hmean : 0 < ∫ r, ψ r ∂overlapLaw d G)
    (hGG : CovarianceGG d G ψ) : ∀ᵐ ω ∂d, G ω ({0} : Set H) = 0 := by
  let a : ℝ := ∫ r, ψ r ∂overlapLaw d G
  let T := zeroStarMass d G ψ
  have hψint : Integrable ψ (overlapLaw d G) := by
    apply Integrable.of_bound hψ.measurable.aestronglyMeasurable D
    exact (overlapLaw_ae_Icc d G hball).mono fun r hr => by
      simpa only [Real.norm_eq_abs] using hbound r hr
  have hTnonneg : ∀ m, 0 ≤ T m := fun _ => measureReal_nonneg
  have hrec : ∀ m, T (m + 1) ≤ (1 - (a / C) / ((m : ℝ) + 1)) * T m := by
    intro m
    let μ := law d G (m + 2)
    let f : (Fin (m + 2) → H) → ℝ := fun σ => zeroStarIndicator ψ m (initial σ)
    let g : (Fin (m + 2) → H) → ℝ := zeroStarIndicator ψ (m + 1)
    have hf : Measurable f := (zeroStarIndicator_measurable hψ m).comp (initial_measurable _)
    have hg : Measurable g := zeroStarIndicator_measurable hψ (m + 1)
    have hfi : Integrable f μ := by
      apply Integrable.of_bound hf.aestronglyMeasurable 1
      exact .of_forall fun σ => by
        change |zeroStarIndicator ψ m (initial σ)| ≤ 1
        rw [abs_of_nonneg (zeroStarIndicator_mem ψ m (initial σ)).1]
        exact (zeroStarIndicator_mem ψ m (initial σ)).2
    have hgi : Integrable g μ := by
      apply Integrable.of_bound hg.aestronglyMeasurable 1
      exact .of_forall fun σ => by
        change |zeroStarIndicator ψ (m + 1) σ| ≤ 1
        rw [abs_of_nonneg (zeroStarIndicator_mem ψ (m + 1) σ).1]
        exact (zeroStarIndicator_mem ψ (m + 1) σ).2
    have hR := overlap_hasLaw d G (0 : Fin (m + 2)) (Fin.last (m + 1))
      (by intro h; have := congrArg Fin.val h; simp at this)
    have hRi : Integrable (fun σ => ψ (GaussianGGStarRecursion.freshOverlap m σ)) μ :=
      hR.integrable_comp hψint
    have hleft : Integrable (fun σ => f σ * ψ (GaussianGGStarRecursion.freshOverlap m σ)) μ := by
      apply hRi.bdd_mul hf.aestronglyMeasurable
      exact .of_forall fun σ => by
        change |zeroStarIndicator ψ m (initial σ)| ≤ 1
        rw [abs_of_nonneg (zeroStarIndicator_mem ψ m (initial σ)).1]
        exact (zeroStarIndicator_mem ψ m (initial σ)).2
    have hup : ∀ᵐ σ ∂μ, ψ (GaussianGGStarRecursion.freshOverlap m σ) ≤ C :=
      (hR.ae_iff (measurableSet_setOfPred.mp (hψ.measurable measurableSet_Iic))).mpr hupper
    have hi := integral_mono_ae hleft ((hfi.sub hgi).const_mul C)
      (hup.mono fun σ hσ => zeroStar_fresh_upper ψ m hC.le σ hσ)
    change (∫ σ, zeroStarIndicator ψ m (initial σ) *
      ψ (GaussianGGStarRecursion.freshOverlap m σ) ∂law d G (m + 2)) ≤ _ at hi
    rw [zeroStar_fresh_identity d G hψ hGG m] at hi
    change a / ((m : ℝ) + 1) * T m ≤ ∫ σ, C * (f σ - g σ) ∂μ at hi
    rw [integral_const_mul, integral_sub hfi hgi] at hi
    have hfmean : (∫ σ, f σ ∂μ) = T m := zeroStarPrefix_integral d G hψ m
    have hgmean : (∫ σ, g σ ∂μ) = T (m + 1) := zeroStarIndicator_integral d G hψ (m + 1)
    rw [hfmean, hgmean] at hi
    change a / ((m : ℝ) + 1) * T m ≤ C * (T m - T (m + 1)) at hi
    have hden : (m : ℝ) + 1 ≠ 0 := by positivity
    have heq : C * ((a / C) / ((m : ℝ) + 1)) = a / ((m : ℝ) + 1) := by
      field_simp
    have heqT := congrArg (fun z : ℝ => z * T m) heq
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith [heqT]
  have hbzero : originMass d G = 0 :=
    zeroStar_common_lower_eq_zero T (div_pos hmean hC)
      (integral_nonneg fun _ => measureReal_nonneg)
      (originMass_le_zeroStarMass d G hψ hψ0) hTnonneg hrec
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => measureReal_nonneg)
    (kernel_origin_integrable d G)).mp hbzero
  filter_upwards [hae] with ω hω
  exact (ENNReal.toReal_eq_zero_iff (G ω ({0} : Set H))).mp hω |>.resolve_right
    (measure_ne_top _ _)

end SlowEquilibration.DirectingPhysical
