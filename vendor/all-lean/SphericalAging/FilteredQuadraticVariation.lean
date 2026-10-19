module

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
public import SphericalAging.VectorIto
public import StochasticCalculus.QuadraticVariationDensity

public section

/-!
# Quadratic variation in an enlarged Brownian filtration

Adapted from Ezzeri Esa's `QuadraticVariation`, `QuadraticVariationElementary`
`QuadraticVariationDensity` and `QuadraticVariationGrid` (Apache 2.0). The natural-filtration equality
is replaced by the actual increment independence `IsFilteredPreBrownian`.
All bracket convergence statements concern the constructed stochastic integral.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped BigOperators ENNReal NNReal InnerProductSpace
namespace SphericalAging.FilteredQuadraticVariation
variable {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
  {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

theorem integral_sq_naturalItoProcessRepresentative_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (s t : ℝ≥0) :
    ∫ ω, (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U t ω -
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω) ^ 2 ∂P =
      ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t -
        FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s‖ ^ 2 := by
  let It := FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t
  let Is := FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s
  calc
    ∫ ω, (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U t ω -
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω) ^ 2 ∂P =
        ∫ ω, ⟪((It - Is : RandomL2 P) : W → ℝ) ω,
          ((It - Is : RandomL2 P) : W → ℝ) ω⟫_ℝ ∂P := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub It Is,
        FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered U t,
        FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered U s]
        with ω hsub ht hs
      change ((It : W → ℝ) ω) =
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U t ω at ht
      change ((Is : W → ℝ) ω) =
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω at hs
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [ht, hs]
      simp [pow_two]
    _ = inner ℝ (It - Is) (It - Is) := (L2.inner_def _ _).symm
    _ = ‖It - Is‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- Orthogonality of Itô-integral increments turns the squared norm of an
increment into a telescoping difference. -/
theorem norm_sq_naturalItoProcess_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t -
        FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s‖ ^ 2 =
      ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t‖ ^ 2 -
        ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s‖ ^ 2 := by
  have ho := FourPapersCommon.FilteredBrownian.inner_naturalItoProcess_sub_naturalItoProcess
    hB hsm hfiltered hst U U
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  rw [norm_sub_sq_real]
  linarith

/-- The squared increments of the chosen representative of a natural Itô
integral process are integrable. -/
theorem integrable_sq_naturalItoProcessRepresentative_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (s t : ℝ≥0) :
    Integrable (fun ω =>
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U t ω -
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω) ^ 2) P := by
  let It := FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t
  let Is := FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s
  have hbase : Integrable (fun ω =>
      (((It - Is : RandomL2 P) : W → ℝ) ω) ^ 2) P :=
    (Lp.memLp (It - Is)).integrable_sq
  apply hbase.congr
  filter_upwards [Lp.coeFn_sub It Is,
    FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered U t,
    FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered U s]
    with ω hsub ht hs
  change ((It : W → ℝ) ω) =
    FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U t ω at ht
  change ((Is : W → ℝ) ω) =
    FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω at hs
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [ht, hs]

/-- Every finite quadratic-variation approximant of a natural Itô integral
has expectation equal to the terminal second moment.  In particular, the
identity is uniform in the partition size, which is the key estimate in the
`PredictableProcessL2` density argument. -/
theorem integral_quadraticVariationApprox_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, quadraticVariationApprox
        (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U) t n ω ∂P =
      ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t‖ ^ 2 := by
  unfold quadraticVariationApprox
  rw [integral_finsetSum]
  · calc
      (∑ i ∈ Finset.range n,
          ∫ ω,
            (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U
                (uniformPartitionTime t n (i + 1)) ω -
              FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U
                (uniformPartitionTime t n i) ω) ^ 2 ∂P) =
          ∑ i ∈ Finset.range n,
            ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
                (uniformPartitionTime t n (i + 1)) -
              FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
                (uniformPartitionTime t n i)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact integral_sq_naturalItoProcessRepresentative_sub
              hB hsm hfiltered U _ _
      _ = ∑ i ∈ Finset.range n,
            (‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
                (uniformPartitionTime t n (i + 1))‖ ^ 2 -
              ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
                (uniformPartitionTime t n i)‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply norm_sq_naturalItoProcess_sub hB hsm hfiltered U
            unfold uniformPartitionTime
            gcongr
            omega
      _ = ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
              (uniformPartitionTime t n n)‖ ^ 2 -
            ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
              (uniformPartitionTime t n 0)‖ ^ 2 := by
            exact Finset.sum_range_sub
              (fun i => ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U
                (uniformPartitionTime t n i)‖ ^ 2) n
      _ = ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U t‖ ^ 2 := by
            have hn0 : (n : ℝ≥0) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt hn
            simp [uniformPartitionTime, hn0]
  · intro i _hi
    exact integrable_sq_naturalItoProcessRepresentative_sub hB hsm hfiltered U _ _


theorem quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (v : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P →₀ ℝ)
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered
        (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v)) P t
      (fun ω => ∑ x ∈ v.support, ∑ y ∈ v.support,
        (v x * (x.2.2 : W → ℝ) ω) * (v y * (y.2.2 : W → ℝ) ω) *
          clippedIntervalCovariation
            x.1 x.2.1.1 y.1 y.2.1.1 t) := by
  classical
  let c : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P → W → ℝ :=
    fun x ω => v x * (x.2.2 : W → ℝ) ω
  have hcMeas : ∀ x ∈ v.support, AEStronglyMeasurable (c x) P := by
    intro x _hx
    exact aestronglyMeasurable_const.mul
      (AEStronglyMeasurable.mono
        (𝓕.le x.1) (lpMeas.aestronglyMeasurable x.2.2))
  have hraw := quadraticVariation_finset_random_brownian_blocks
    hB v.support (fun x => x.1) (fun x => x.2.1.1)
      (fun x _hx => x.2.1.2) c hcMeas t
  apply hraw.congr
  · intro s
    exact (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
      hB.toIsPreBrownianReal hsm hfiltered v s).symm
  · exact Filter.EventuallyEq.rfl

@[expose] noncomputable def nnrealIicIndicator (u s : ℝ≥0) : ℝ :=
  (Set.Iic u).indicator (fun _ => (1 : ℝ)) s

@[expose] noncomputable def nnrealIocIndicator (a b s : ℝ≥0) : ℝ :=
  (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s


omit [IsProbabilityMeasure P] in
theorem elementaryFinsuppToPredictable_coeFn [SFinite P]
    (v : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v :
        ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => ∑ x ∈ v.support, v x *
        nnrealIocIndicator x.1 x.2.1.1 p.1 *
          (x.2.2 : W → ℝ) p.2 := by
  rw [show FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v =
      ∑ x ∈ v.support, v x •
        FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x by
    unfold FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable
    rfl]
  have hsum := Lp.coeFn_fun_finsetSum v.support
    (fun x => v x •
      (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x :
        TimeProcessL2 P))
  have hterm : ∀ x ∈ v.support,
      (((v x) • (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator
        𝓕 P x : TimeProcessL2 P) : TimeProcessL2 P) :
          ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p => v x * nnrealIocIndicator x.1 x.2.1.1 p.1 *
          (x.2.2 : W → ℝ) p.2 := by
    intro x _hx
    have helem := elementaryPredictable_coeFn
      𝓕 x.1 x.2.1.1 x.2.2
    filter_upwards [Lp.coeFn_smul (v x)
        (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator
          𝓕 P x : TimeProcessL2 P),
      helem] with p hsmul helem'
    rw [hsmul]
    change v x * ((elementaryPredictable 𝓕
      x.1 x.2.1.1 x.2.2 : TimeProcessL2 P) : ℝ≥0 × W → ℝ) p = _
    change (elementaryPredictable 𝓕
      x.1 x.2.1.1 x.2.2 : ℝ≥0 × W → ℝ) p = _ at helem'
    rw [helem']
    unfold nnrealIocIndicator
    by_cases hp : p.1 ∈ Set.Ioc x.1 x.2.1.1 <;> simp [hp]
  filter_upwards [hsum, v.support.eventually_all.mpr hterm] with p hs hp
  have hcoe : ((∑ x ∈ v.support, v x •
      FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x :
        PredictableProcessL2 𝓕 P) : TimeProcessL2 P) =
      ∑ x ∈ v.support, v x •
        (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x :
          TimeProcessL2 P) := by
    change (lpMeas ℝ ℝ 𝓕.predictable 2
      (nonnegativeLebesgueMeasure.prod P)).subtype
        (∑ x ∈ v.support, v x •
          FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x) = _
    rw [map_sum]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro x _hx
    rfl
  rw [hcoe]
  rw [hs]
  apply Finset.sum_congr rfl
  intro x hx
  exact hp x hx

/-- The canonical time integral of the square of a predictable `L²` process,
using its selected product-space representative. -/
@[expose] noncomputable def predictableQuadraticVariation
    (U : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) (ω : W) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) t, ((U : ℝ≥0 × W → ℝ) (s, ω)) ^ 2
    ∂nonnegativeLebesgueMeasure

/-- The predictable bracket of a formal finite combination is, almost surely,
the double sum of weighted clipped covariations. -/
theorem predictableQuadraticVariation_elementaryFinsuppToPredictable
    (v : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P →₀ ℝ)
    (t : ℝ≥0) :
    predictableQuadraticVariation
        (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v) t =ᵐ[P]
      fun ω => ∑ x ∈ v.support, ∑ y ∈ v.support,
        (v x * (x.2.2 : W → ℝ) ω) * (v y * (y.2.2 : W → ℝ) ω) *
          clippedIntervalCovariation x.1 x.2.1.1 y.1 y.2.1.1 t := by
  classical
  let U := FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v
  have hcoe := elementaryFinsuppToPredictable_coeFn v
  have hswap := (Measure.measurePreserving_swap
    (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hcoe
  have hswap' :
      (fun p : W × ℝ≥0 => (U : ℝ≥0 × W → ℝ) p.swap) =ᵐ[
        P.prod nonnegativeLebesgueMeasure]
      fun p => ∑ x ∈ v.support, v x *
        nnrealIocIndicator x.1 x.2.1.1 p.2 * (x.2.2 : W → ℝ) p.1 := by
    simpa [U, Function.comp_def] using hswap
  have hsections := Measure.ae_ae_of_ae_prod hswap'
  filter_upwards [hsections] with ω hω
  unfold predictableQuadraticVariation
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((U : ℝ≥0 × W → ℝ) (s, ω)) ^ 2
        ∂nonnegativeLebesgueMeasure) =
        ∫ s in Set.Ioc (0 : ℝ≥0) t,
          (∑ x ∈ v.support,
            (v x * (x.2.2 : W → ℝ) ω) *
              nnrealIocIndicator x.1 x.2.1.1 s) ^ 2
          ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hω] with s hs
      have hs' : (U : ℝ≥0 × W → ℝ) (s, ω) =
          ∑ x ∈ v.support, v x *
            nnrealIocIndicator x.1 x.2.1.1 s *
              (x.2.2 : W → ℝ) ω := by
        simpa only [Prod.swap_prod_mk] using hs
      rw [hs']
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x ∈ v.support, ∑ y ∈ v.support,
        (v x * (x.2.2 : W → ℝ) ω) * (v y * (y.2.2 : W → ℝ) ω) *
          clippedIntervalCovariation x.1 x.2.1.1 y.1 y.2.1.1 t := by
      exact integral_sq_finset_nnrealIocIndicator v.support
        (fun x => x.1) (fun x => x.2.1.1)
        (fun x hx => x.2.1.2)
        (fun x => v x * (x.2.2 : W → ℝ) ω) t

/-- The natural Itô representative of a formal finite combination has quadratic
variation in probability equal to its predictable bracket. -/
theorem quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp_bracket
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (v : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P →₀ ℝ)
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered
        (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v)) P t
      (predictableQuadraticVariation
        (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v) t) := by
  apply (quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp
    hB hsm hfiltered v t).congr
  · intro s
    exact Filter.EventuallyEq.rfl
  · exact (predictableQuadraticVariation_elementaryFinsuppToPredictable v t).symm


theorem naturalItoProcessRepresentative_add_ae
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U V : PredictableProcessL2 𝓕 P) (s : ℝ≥0) :
    (fun ω => FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω +
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered V s ω) =ᵐ[P]
      FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered (U + V) s := by
  have hU := FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered U s
  have hV := FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered V s
  have hS := FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative hB hsm hfiltered (U + V) s
  have hlin : FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered (U + V) s =
      FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s +
        FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered V s := by
    unfold FourPapersCommon.FilteredBrownian.naturalItoProcess
    rw [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_add, map_add]
  have hcoe := Lp.coeFn_add (FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s)
    (FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered V s)
  filter_upwards [hU, hV, hS, hcoe] with ω hUω hVω hSω hcoeω
  change (FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered U s : W → ℝ) ω =
    FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U s ω at hUω
  change (FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered V s : W → ℝ) ω =
    FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered V s ω at hVω
  change (FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered (U + V) s : W → ℝ) ω =
    FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered (U + V) s ω at hSω
  rw [← hUω, ← hVω, ← hSω, hlin, hcoeω]
  rfl

theorem integrable_quadraticVariationApprox_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) (n : ℕ) :
    Integrable (quadraticVariationApprox
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U) t n) P := by
  unfold quadraticVariationApprox
  exact integrable_finsetSum (Finset.range n) (fun i _hi =>
    integrable_sq_naturalItoProcessRepresentative_sub hB hsm hfiltered U _ _)

theorem integral_abs_quadraticVariationApprox_sub_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U V : PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, |quadraticVariationApprox
          (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U) t n ω -
        quadraticVariationApprox
          (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered V) t n ω| ∂P ≤
      ‖U - V‖ * ‖U + V‖ := by
  let X := FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered U
  let Y := FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered V
  let D := FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered (U - V)
  let S := FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB hsm hfiltered (U + V)
  let QX := quadraticVariationApprox X t n
  let QY := quadraticVariationApprox Y t n
  let QD := quadraticVariationApprox D t n
  let QS := quadraticVariationApprox S t n
  have hDprocess : ∀ s, (fun ω => X s ω - Y s ω) =ᵐ[P] D s := by
    intro s
    simpa only [X, Y, D] using
      FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_sub_ae hB hsm hfiltered U V s
  have hSprocess : ∀ s, (fun ω => X s ω + Y s ω) =ᵐ[P] S s := by
    intro s
    simpa only [X, Y, S] using
      naturalItoProcessRepresentative_add_ae hB hsm hfiltered U V s
  have hQD : quadraticVariationApprox
      (fun s ω => X s ω - Y s ω) t n =ᵐ[P] QD := by
    simpa only [QD] using quadraticVariationApprox_congr_ae hDprocess t n
  have hQS : quadraticVariationApprox
      (fun s ω => X s ω + Y s ω) t n =ᵐ[P] QS := by
    simpa only [QS] using quadraticVariationApprox_congr_ae hSprocess t n
  have hQXint : Integrable QX P := by
    simpa only [QX, X] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm hfiltered U t n
  have hQYint : Integrable QY P := by
    simpa only [QY, Y] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm hfiltered V t n
  have hQDint : Integrable QD P := by
    simpa only [QD, D] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm hfiltered (U - V) t n
  have hQSint : Integrable QS P := by
    simpa only [QS, S] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm hfiltered (U + V) t n
  have hDtime : ∀ s, AEStronglyMeasurable (D s) P := fun s =>
    by
      simpa only [D] using AEStronglyMeasurable.mono
        (𝓕.le s)
        (StronglyMeasurable.aestronglyMeasurable
          (FourPapersCommon.FilteredBrownian.stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm hfiltered (U - V) s))
  have hStime : ∀ s, AEStronglyMeasurable (S s) P := fun s =>
    by
      simpa only [S] using AEStronglyMeasurable.mono
        (𝓕.le s)
        (StronglyMeasurable.aestronglyMeasurable
          (FourPapersCommon.FilteredBrownian.stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm hfiltered (U + V) s))
  have hQDmeas : AEStronglyMeasurable QD P := by
    simpa only [QD] using aestronglyMeasurable_quadraticVariationApprox hDtime t n
  have hQSmeas : AEStronglyMeasurable QS P := by
    simpa only [QS] using aestronglyMeasurable_quadraticVariationApprox hStime t n
  have hsqrtQDmeas : AEStronglyMeasurable (fun ω => Real.sqrt (QD ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQDmeas
  have hsqrtQSmeas : AEStronglyMeasurable (fun ω => Real.sqrt (QS ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQSmeas
  have hsqrtQDmem : MemLp (fun ω => Real.sqrt (QD ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hsqrtQDmeas).2
    apply hQDint.congr
    filter_upwards with ω
    rw [Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg D t n ω
  have hsqrtQSmem : MemLp (fun ω => Real.sqrt (QS ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hsqrtQSmeas).2
    apply hQSint.congr
    filter_upwards with ω
    rw [Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg S t n ω
  have hpoint : (fun ω => |QX ω - QY ω|) ≤ᵐ[P]
      fun ω => Real.sqrt (QD ω) * Real.sqrt (QS ω) := by
    filter_upwards [hQD, hQS] with ω hQDω hQSω
    calc
      |QX ω - QY ω| =
          |quadraticCovariationApprox
            (fun s ω => X s ω - Y s ω)
            (fun s ω => X s ω + Y s ω) t n ω| := by
        rw [← quadraticVariationApprox_sub_eq_covariation_sub_add]
      _ ≤ Real.sqrt
          (quadraticVariationApprox (fun s ω => X s ω - Y s ω) t n ω *
            quadraticVariationApprox (fun s ω => X s ω + Y s ω) t n ω) :=
        Real.abs_le_sqrt (quadraticCovariationApprox_sq_le _ _ t n ω)
      _ = Real.sqrt (QD ω) * Real.sqrt (QS ω) := by
        rw [hQDω, hQSω, Real.sqrt_mul]
        exact quadraticVariationApprox_nonneg D t n ω
  have hleftint : Integrable (fun ω => |QX ω - QY ω|) P :=
    (hQXint.sub hQYint).abs
  have hrightint : Integrable
      (fun ω => Real.sqrt (QD ω) * Real.sqrt (QS ω)) P := by
    change Integrable
      ((fun ω => Real.sqrt (QD ω)) * (fun ω => Real.sqrt (QS ω))) P
    exact hsqrtQDmem.integrable_mul hsqrtQSmem
  have hsqrtQDmem' : MemLp (fun ω => Real.sqrt (QD ω))
      (ENNReal.ofReal (2 : ℝ)) P := by
    simpa only [ENNReal.ofReal_ofNat] using hsqrtQDmem
  have hsqrtQSmem' : MemLp (fun ω => Real.sqrt (QS ω))
      (ENNReal.ofReal (2 : ℝ)) P := by
    simpa only [ENNReal.ofReal_ofNat] using hsqrtQSmem
  have hsqrtQDpow :
      (fun ω => (Real.sqrt (QD ω)) ^ (2 : ℝ)) =ᵐ[P] QD := by
    filter_upwards with ω
    rw [Real.rpow_two, Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg D t n ω
  have hsqrtQSpow :
      (fun ω => (Real.sqrt (QS ω)) ^ (2 : ℝ)) =ᵐ[P] QS := by
    filter_upwards with ω
    rw [Real.rpow_two, Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg S t n ω
  calc
    (∫ ω, |QX ω - QY ω| ∂P) ≤
        ∫ ω, Real.sqrt (QD ω) * Real.sqrt (QS ω) ∂P :=
      integral_mono_ae hleftint hrightint hpoint
    _ ≤ (∫ ω, (Real.sqrt (QD ω)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫ ω, (Real.sqrt (QS ω)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
      exact integral_mul_le_Lp_mul_Lq_of_nonneg
        Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
        (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
        hsqrtQDmem' hsqrtQSmem'
    _ = Real.sqrt (∫ ω, QD ω ∂P) * Real.sqrt (∫ ω, QS ω ∂P) := by
      rw [integral_congr_ae hsqrtQDpow, integral_congr_ae hsqrtQSpow]
      norm_num [← Real.sqrt_eq_rpow]
    _ = ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered (U - V) t‖ *
        ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered (U + V) t‖ := by
      rw [show (∫ ω, QD ω ∂P) =
          ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered (U - V) t‖ ^ 2 by
        simpa only [QD, D] using
          integral_quadraticVariationApprox_naturalItoProcessRepresentative
            hB hsm hfiltered (U - V) t hn,
        show (∫ ω, QS ω ∂P) =
          ‖FourPapersCommon.FilteredBrownian.naturalItoProcess hB hsm hfiltered (U + V) t‖ ^ 2 by
        simpa only [QS, S] using
          integral_quadraticVariationApprox_naturalItoProcessRepresentative
            hB hsm hfiltered (U + V) t hn]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ ‖U - V‖ * ‖U + V‖ := by
      exact mul_le_mul
        (FourPapersCommon.FilteredBrownian.norm_naturalItoProcess_le hB hsm hfiltered (U - V) t)
        (FourPapersCommon.FilteredBrownian.norm_naturalItoProcess_le hB hsm hfiltered (U + V) t)
        (norm_nonneg _) (norm_nonneg _)

omit [IsProbabilityMeasure P] in
theorem integral_sq_predictableProcess_eq_norm_sq
    (U : PredictableProcessL2 𝓕 P) :
    ∫ p, ((U : ℝ≥0 × W → ℝ) p) ^ 2
        ∂(nonnegativeLebesgueMeasure.prod P) = ‖U‖ ^ 2 := by
  calc
    (∫ p, ((U : ℝ≥0 × W → ℝ) p) ^ 2
        ∂(nonnegativeLebesgueMeasure.prod P)) =
        inner ℝ (U : TimeProcessL2 P) (U : TimeProcessL2 P) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with p
      simp [pow_two]
    _ = ‖(U : TimeProcessL2 P)‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖U‖ ^ 2 := rfl

theorem integrable_predictableQuadraticVariation
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    Integrable (predictableQuadraticVariation U t) P := by
  let Q := nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)
  have hsq : Integrable (fun p : ℝ≥0 × W =>
      ((U : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : TimeProcessL2 P)).integrable_sq
  have hmeasure : Q.prod P ≤ nonnegativeLebesgueMeasure.prod P := by
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hsqQ := hsq.mono_measure hmeasure
  have houter := hsqQ.integral_prod_right
  change Integrable (fun y => ∫ x in Set.Ioc (0 : ℝ≥0) t,
    ((U : ℝ≥0 × W → ℝ) (x, y)) ^ 2 ∂nonnegativeLebesgueMeasure) P
  exact houter

omit [IsProbabilityMeasure P] in
theorem predictableProcess_coeFn_sub
    (U V : PredictableProcessL2 𝓕 P) :
    ((U - V : PredictableProcessL2 𝓕 P) :
        ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => (U : ℝ≥0 × W → ℝ) p - (V : ℝ≥0 × W → ℝ) p := by
  have hsub : ((U - V : PredictableProcessL2
      𝓕 P) : TimeProcessL2 P) =
      (U : TimeProcessL2 P) - (V : TimeProcessL2 P) := by
    change (lpMeas ℝ ℝ 𝓕.predictable 2
      (nonnegativeLebesgueMeasure.prod P)).subtype (U - V) = _
    rw [map_sub]
    rfl
  rw [show ((U - V : PredictableProcessL2
      𝓕 P) : ℝ≥0 × W → ℝ) =
      (((U - V : PredictableProcessL2
        𝓕 P) : TimeProcessL2 P) :
          ℝ≥0 × W → ℝ) by rfl, hsub]
  filter_upwards [Lp.coeFn_sub (U : TimeProcessL2 P)
      (V : TimeProcessL2 P)] with p hp
  simpa only [Pi.sub_apply] using hp

omit [IsProbabilityMeasure P] in
theorem predictableProcess_coeFn_add
    (U V : PredictableProcessL2 𝓕 P) :
    ((U + V : PredictableProcessL2 𝓕 P) :
        ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => (U : ℝ≥0 × W → ℝ) p + (V : ℝ≥0 × W → ℝ) p := by
  have hadd : ((U + V : PredictableProcessL2
      𝓕 P) : TimeProcessL2 P) =
      (U : TimeProcessL2 P) + (V : TimeProcessL2 P) := by
    change (lpMeas ℝ ℝ 𝓕.predictable 2
      (nonnegativeLebesgueMeasure.prod P)).subtype (U + V) = _
    rw [map_add]
    rfl
  rw [show ((U + V : PredictableProcessL2
      𝓕 P) : ℝ≥0 × W → ℝ) =
      (((U + V : PredictableProcessL2
        𝓕 P) : TimeProcessL2 P) :
          ℝ≥0 × W → ℝ) by rfl, hadd]
  filter_upwards [Lp.coeFn_add (U : TimeProcessL2 P)
      (V : TimeProcessL2 P)] with p hp
  simpa only [Pi.add_apply] using hp

theorem integral_abs_predictableQuadraticVariation_sub_le
    (U V : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ∫ ω, |predictableQuadraticVariation U t ω -
        predictableQuadraticVariation V t ω| ∂P ≤
      ‖U - V‖ * ‖U + V‖ := by
  let Q := nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)
  let F : ℝ≥0 × W → ℝ := fun p =>
    (U : ℝ≥0 × W → ℝ) p - (V : ℝ≥0 × W → ℝ) p
  let G : ℝ≥0 × W → ℝ := fun p =>
    (U : ℝ≥0 × W → ℝ) p + (V : ℝ≥0 × W → ℝ) p
  let A : ℝ≥0 × W → ℝ := fun p =>
    |((U : ℝ≥0 × W → ℝ) p) ^ 2 - ((V : ℝ≥0 × W → ℝ) p) ^ 2|
  have hFmem : MemLp F 2 (nonnegativeLebesgueMeasure.prod P) := by
    dsimp only [F]
    exact (Lp.memLp (U : TimeProcessL2 P)).sub (Lp.memLp (V : TimeProcessL2 P))
  have hGmem : MemLp G 2 (nonnegativeLebesgueMeasure.prod P) := by
    dsimp only [G]
    exact (Lp.memLp (U : TimeProcessL2 P)).add (Lp.memLp (V : TimeProcessL2 P))
  have hAeq : A = fun p => |F p * G p| := by
    funext p
    dsimp only [A, F, G]
    congr 1
    ring
  have hAint : Integrable A (nonnegativeLebesgueMeasure.prod P) := by
    rw [hAeq]
    exact (hFmem.integrable_mul hGmem).abs
  have hmeasure : Q.prod P ≤ nonnegativeLebesgueMeasure.prod P := by
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hAQint := hAint.mono_measure hmeasure
  have hU2int : Integrable (fun p : ℝ≥0 × W =>
      ((U : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : TimeProcessL2 P)).integrable_sq
  have hV2int : Integrable (fun p : ℝ≥0 × W =>
      ((V : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (V : TimeProcessL2 P)).integrable_sq
  have hU2Qint := hU2int.mono_measure hmeasure
  have hV2Qint := hV2int.mono_measure hmeasure
  have hpoint : (fun ω => |predictableQuadraticVariation U t ω -
      predictableQuadraticVariation V t ω|) ≤ᵐ[P]
      fun ω => ∫ s, A (s, ω) ∂Q := by
    filter_upwards [hU2Qint.prod_left_ae, hV2Qint.prod_left_ae]
      with ω hUω hVω
    unfold predictableQuadraticVariation
    change |(∫ s, ((U : ℝ≥0 × W → ℝ) (s, ω)) ^ 2 ∂Q) -
        ∫ s, ((V : ℝ≥0 × W → ℝ) (s, ω)) ^ 2 ∂Q| ≤ _
    rw [← integral_sub hUω hVω]
    exact abs_integral_le_integral_abs
  have hleftint : Integrable (fun ω =>
      |predictableQuadraticVariation U t ω -
        predictableQuadraticVariation V t ω|) P :=
    ((integrable_predictableQuadraticVariation U t).sub
      (integrable_predictableQuadraticVariation V t)).abs
  have hrightint : Integrable (fun ω => ∫ s, A (s, ω) ∂Q) P :=
    hAQint.integral_prod_right
  have hFmem' : MemLp F (ENNReal.ofReal (2 : ℝ))
      (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [ENNReal.ofReal_ofNat] using hFmem
  have hGmem' : MemLp G (ENNReal.ofReal (2 : ℝ))
      (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [ENNReal.ofReal_ofNat] using hGmem
  have hFintSq :
      (∫ p, ‖F p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
        ‖U - V‖ ^ 2 := by
    calc
      (∫ p, ‖F p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
          ∫ p, F p ^ 2 ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      _ = ∫ p, (((U - V : PredictableProcessL2
          𝓕 P) : ℝ≥0 × W → ℝ) p) ^ 2
          ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards [predictableProcess_coeFn_sub U V]
          with p hp
        rw [hp]
      _ = ‖U - V‖ ^ 2 :=
        integral_sq_predictableProcess_eq_norm_sq (U - V)
  have hGintSq :
      (∫ p, ‖G p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
        ‖U + V‖ ^ 2 := by
    calc
      (∫ p, ‖G p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
          ∫ p, G p ^ 2 ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      _ = ∫ p, (((U + V : PredictableProcessL2
          𝓕 P) : ℝ≥0 × W → ℝ) p) ^ 2
          ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards [predictableProcess_coeFn_add U V]
          with p hp
        rw [hp]
      _ = ‖U + V‖ ^ 2 :=
        integral_sq_predictableProcess_eq_norm_sq (U + V)
  calc
    (∫ ω, |predictableQuadraticVariation U t ω -
        predictableQuadraticVariation V t ω| ∂P) ≤
        ∫ ω, ∫ s, A (s, ω) ∂Q ∂P :=
      integral_mono_ae hleftint hrightint hpoint
    _ = ∫ p, A p ∂(Q.prod P) :=
      (integral_prod_symm A hAQint).symm
    _ ≤ ∫ p, A p ∂(nonnegativeLebesgueMeasure.prod P) :=
      integral_mono_measure hmeasure
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hAint
    _ = ∫ p, ‖F p‖ * ‖G p‖
        ∂(nonnegativeLebesgueMeasure.prod P) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hAeq]
      simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ (∫ p, ‖F p‖ ^ (2 : ℝ)
          ∂(nonnegativeLebesgueMeasure.prod P)) ^ (1 / (2 : ℝ)) *
        (∫ p, ‖G p‖ ^ (2 : ℝ)
          ∂(nonnegativeLebesgueMeasure.prod P)) ^ (1 / (2 : ℝ)) := by
      exact integral_mul_norm_le_Lp_mul_Lq
        Real.HolderConjugate.two_two hFmem' hGmem'
    _ = ‖U - V‖ * ‖U + V‖ := by
      rw [hFintSq, hGintSq]
      norm_num [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]


theorem quadraticVariation_naturalItoProcessRepresentative
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered U) P t
      (predictableQuadraticVariation U t) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let e := FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P
  have hUdense : U ∈ closure (Set.range e) :=
    (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable (P := P)
      𝓕) U
  obtain ⟨Uk, hUkRange, hUk⟩ := mem_closure_iff_seq_limit.mp hUdense
  choose v hv using hUkRange
  let f : ℕ → W → ℝ := fun n => quadraticVariationApprox
    (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered U) t (n + 1)
  let g : W → ℝ := predictableQuadraticVariation U t
  let F : ℕ → ℕ → W → ℝ := fun k n => quadraticVariationApprox
    (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm hfiltered (Uk k))
      t (n + 1)
  let G : ℕ → W → ℝ := fun k => predictableQuadraticVariation (Uk k) t
  let a : ℕ → ℝ := fun k => ‖U - Uk k‖ * ‖U + Uk k‖
  have ha : Tendsto a Filter.atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => U) Filter.atTop (nhds U) :=
      tendsto_const_nhds
    have hsub := hconst.sub hUk
    have hadd := hconst.add hUk
    have hmul := hsub.norm.mul hadd.norm
    simpa only [a, sub_self, norm_zero, zero_mul] using hmul
  have hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k) := by
    intro k
    have hk := quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp_bracket
      hB hsm hfiltered (v k) t
    rw [hv k] at hk
    simpa only [HasQuadraticVariationInProbabilityAt, F, G] using hk
  change TendstoInMeasure P f Filter.atTop g
  apply tendstoInMeasure_of_uniform_integral_approx f g F G a ha
  · intro k
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact hFG
  · intro k n
    have hU :=
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm hfiltered U t (n + 1)
    have hUk :=
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm hfiltered (Uk k) t (n + 1)
    dsimp only [f, F]
    apply ((hU.sub hUk).norm).congr
    filter_upwards with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  · intro k n
    simpa only [f, F, a, Real.norm_eq_abs] using
      integral_abs_quadraticVariationApprox_sub_le
        hB.toIsPreBrownianReal hsm hfiltered U (Uk k) t (Nat.zero_lt_succ n)
  · intro k
    have hUkInt := integrable_predictableQuadraticVariation (Uk k) t
    have hUInt := integrable_predictableQuadraticVariation U t
    dsimp only [G, g]
    apply ((hUkInt.sub hUInt).norm).congr
    filter_upwards with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  · intro k
    simpa only [G, g, a, Real.norm_eq_abs, abs_sub_comm] using
      integral_abs_predictableQuadraticVariation_sub_le U (Uk k) t


theorem predictableQuadraticVariation_timeRestrict_ae
    (U : PredictableProcessL2 𝓕 P)
    (a t : ℝ≥0) :
    predictableQuadraticVariation
        (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a U) t =ᵐ[P]
      predictableQuadraticVariation U (min t a) := by
  have hswap := (Measure.measurePreserving_swap
    (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp
      (FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn 𝓕 a U)
  have hsections := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hsections] with omega homega
  unfold predictableQuadraticVariation
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a U :
          ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) =
        ∫ s in Set.Ioc (0 : ℝ≥0) t,
          ((FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := W) a).indicator
            (U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
          ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae homega] with s hs
      have hs' :
          (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a U :
            ℝ≥0 × W → ℝ) (s, omega) =
          (FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := W) a).indicator
            (U : ℝ≥0 × W → ℝ) (s, omega) := by
        simpa only [Function.comp_apply, Prod.swap_prod_mk] using hs
      rw [hs']
    _ = ∫ s in Set.Ioc (0 : ℝ≥0) (min t a),
          ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
          ∂nonnegativeLebesgueMeasure := by
      rw [← integral_indicator measurableSet_Ioc,
        ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with s
      by_cases hst : s ∈ Set.Ioc (0 : ℝ≥0) t
      · by_cases hsa : s ∈ Set.Ioc (0 : ℝ≥0) a
        · have hmin : s ∈ Set.Ioc (0 : ℝ≥0) (min t a) :=
            ⟨hst.1, le_min hst.2 hsa.2⟩
          rw [Set.indicator_of_mem hst, Set.indicator_of_mem hmin,
            Set.indicator_of_mem]
          exact ⟨hsa, Set.mem_univ _⟩
        · have hmin : s ∉ Set.Ioc (0 : ℝ≥0) (min t a) := by
            intro hs
            exact hsa ⟨hs.1, hs.2.trans (min_le_right t a)⟩
          rw [Set.indicator_of_mem hst, Set.indicator_of_notMem hmin,
            Set.indicator_of_notMem]
          · norm_num
          · exact fun hs => hsa hs.1
      · have hmin : s ∉ Set.Ioc (0 : ℝ≥0) (min t a) := by
          intro hs
          exact hst ⟨hs.1, hs.2.trans (min_le_left t a)⟩
        rw [Set.indicator_of_notMem hst, Set.indicator_of_notMem hmin]


end SphericalAging.FilteredQuadraticVariation
