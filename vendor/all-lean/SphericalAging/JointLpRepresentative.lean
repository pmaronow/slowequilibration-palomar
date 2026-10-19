module

public import SphericalAging.PicardDependence
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

public section

/-! A jointly strongly measurable representative of any strongly measurable
family of actual L² classes. Geometrically fast measurable simple selection
and the proved L² completeness argument identify every parameter slice.
This is required to pass from quenched SDE classes to random disorder.
-/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.JointLpRepresentative
local infixr:25 " →ₛ " => SimpleFunc
set_option maxHeartbeats 1800000
variable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure Ω}

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma simple_joint_stronglyMeasurable (f : A →ₛ Lp E 2 μ) :
    StronglyMeasurable (fun q : A × Ω => (f q.1 : Ω → E) q.2) := by
  exact ((f.comp Prod.fst measurable_fst).measurable_bind
    (fun v q => (v : Ω → E) q.2)
    (fun v => (Lp.stronglyMeasurable v).measurable.comp measurable_snd)).stronglyMeasurable

section Selection
variable (f : A → Lp E 2 μ) (hf : StronglyMeasurable f)
local notation "r" => (1 / 2 : ℝ)

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma exists_fast_approx (a : A) (n : ℕ) : ∃ m : ℕ, dist (hf.approx m a) (f a) < r^n := by
  exact (Metric.tendsto_nhds.mp (hf.tendsto_approx a) (r^n) (by positivity)).exists

@[expose] def fastIndex (n : ℕ) (a : A) : ℕ := Nat.find (exists_fast_approx f hf a n)

@[expose] def fastClass (n : ℕ) (a : A) : Lp E 2 μ := hf.approx (fastIndex f hf n a) a

lemma fastClass_bound (n : ℕ) (a : A) : dist (fastClass f hf n a) (f a) < r^n :=
  Nat.find_spec (exists_fast_approx f hf a n)

lemma measurable_fastIndex (n : ℕ) : Measurable (fastIndex f hf n) := by
  let : MeasurableSpace (Lp E 2 μ) := borel (Lp E 2 μ)
  have : BorelSpace (Lp E 2 μ) := ⟨rfl⟩
  exact measurable_find (exists_fast_approx f hf · n)
    (fun m => measurableSet_lt (((hf.approx m).stronglyMeasurable.dist hf).measurable) measurable_const)

lemma fast_joint_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun q : A × Ω => (fastClass f hf n q.1 : Ω → E) q.2) := by
  have hm : Measurable (fun q : ℕ × (A × Ω) => ((hf.approx q.1 q.2.1 : Lp E 2 μ) : Ω → E) q.2.2) :=
    measurable_from_prod_countable_right (fun m => (simple_joint_stronglyMeasurable (hf.approx m)).measurable)
  exact (hm.comp (((measurable_fastIndex f hf n).comp measurable_fst).prodMk measurable_id)).stronglyMeasurable

lemma fastClass_tendsto (a : A) : Tendsto (fun n => fastClass f hf n a) atTop (𝓝 (f a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hr : Tendsto (fun n : ℕ => r^n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hr.eventually (eventually_lt_nhds hε)] with n hn
  exact (fastClass_bound f hf n a).trans hn

@[expose] def jointVersion (q : A × Ω) : E := limUnder atTop (fun n => (fastClass f hf n q.1 : Ω → E) q.2)

lemma jointVersion_stronglyMeasurable : StronglyMeasurable (jointVersion f hf) :=
  StronglyMeasurable.limUnder (fast_joint_stronglyMeasurable f hf)

lemma fastClass_eLpNorm_sub (a : A) (n m : ℕ) :
    eLpNorm (fun ω => (fastClass f hf n a : Ω → E) ω - (fastClass f hf m a : Ω → E) ω) 2 μ =
      ENNReal.ofReal ‖fastClass f hf n a - fastClass f hf m a‖ := by
  rw [ofReal_norm, Lp.enorm_def]
  exact eLpNorm_congr_ae (Lp.coeFn_sub (fastClass f hf n a) (fastClass f hf m a)).symm

lemma fastClass_cauchy_bound (a : A) (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) :
    eLpNorm (fun ω => (fastClass f hf n a : Ω → E) ω - (fastClass f hf m a : Ω → E) ω) 2 μ <
      (4 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)^N := by
  rw [fastClass_eLpNorm_sub]
  have hnr : r^n ≤ r^N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hmr : r^m ≤ r^N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hd : ‖fastClass f hf n a-fastClass f hf m a‖ < 4*r^N := by
    rw [← dist_eq_norm]
    have hh := dist_triangle (fastClass f hf n a) (f a) (fastClass f hf m a)
    have hnb := fastClass_bound f hf n a
    have hmb := fastClass_bound f hf m a
    rw [dist_comm (f a)] at hh
    nlinarith [pow_pos (by norm_num : 0 < r) N]
  have heq : (4 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)^N = ENNReal.ofReal (4*r^N) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [heq]
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hd

lemma fast_geometric_tsum_ne_top : (∑' N : ℕ, (4 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)^N) ≠ ∞ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  norm_num

/-- Every parameter slice of the jointly measurable selector represents
its actual L² class. No joint representative is postulated in the data. -/
theorem jointVersion_ae (a : A) : (fun ω => jointVersion f hf (a, ω)) =ᵐ[μ] (f a : Ω → E) := by
  let g (n : ℕ) : Ω → E := fastClass f hf n a
  have hga : ∀ n, AEStronglyMeasurable (g n) μ := fun n => Lp.aestronglyMeasurable (fastClass f hf n a)
  have hB := fast_geometric_tsum_ne_top
  have hlim := Lp.ae_tendsto_of_cauchy_eLpNorm hga (by norm_num : (1 : ℝ≥0∞) ≤ 2) hB
    (fastClass_cauchy_bound f hf a)
  have hlim' : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (jointVersion f hf (a, ω))) := by
    filter_upwards [hlim] with ω hω
    obtain ⟨l, hl⟩ := hω
    change Tendsto (fun n => g n ω) atTop (𝓝 (limUnder atTop (fun n => g n ω)))
    rw [hl.limUnder_eq]
    exact hl
  have hnorm := Lp.cauchy_tendsto_of_tendsto hga (fun ω => jointVersion f hf (a, ω)) hB
    (fastClass_cauchy_bound f hf a) hlim'
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hnorm)
    (tendstoInMeasure_of_tendsto_Lp (fastClass_tendsto f hf a))

end Selection

/-- An actual strongly measurable family of L² classes admits a jointly
strongly measurable version representing every deterministic parameter. -/
theorem exists_joint_representative (f : A → Lp E 2 μ) (hf : StronglyMeasurable f) :
    ∃ G : A × Ω → E, StronglyMeasurable G ∧ ∀ a, (fun ω => G (a, ω)) =ᵐ[μ] (f a : Ω → E) :=
  ⟨jointVersion f hf, jointVersion_stronglyMeasurable f hf, jointVersion_ae f hf⟩

end SphericalAging.JointLpRepresentative
