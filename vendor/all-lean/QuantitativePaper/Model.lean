module
public import Paper.PhysicalSKBridge
public import FRSB.ConstantMassStochasticIntegrability
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

/-! Actual zero-field triangular SK observables and their independent diagonal
completion. All expectations use the concrete product standard Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
namespace QuantitativePaper

abbrev Configuration (n : ℕ) := Paper.SKConfiguration n
abbrev Edge (n : ℕ) := Paper.SKEdge n
abbrev Couplings (n : ℕ) := Paper.SKCouplings n
abbrev couplingLaw (n : ℕ) : Measure (Couplings n) := Paper.skCouplingLaw n

/-- The exact physical Hamiltonian, with one independent coupling per i<j. -/
def energy (n : ℕ) (g : Couplings n) (σ : Configuration n) : ℝ :=
  Paper.skHamiltonian 1 0 g σ

def logPartition (n : ℕ) (β : ℝ) (g : Couplings n) : ℝ :=
  Real.log (Paper.skPartitionFunction β 0 g)

def groundState (n : ℕ) (g : Couplings n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (energy n g)

def energyFreeEnergy (n : ℕ) (β : ℝ) (g : Couplings n) : ℝ := logPartition n β g/β

def pressure (n : ℕ) (β : ℝ) : ℝ := (∫ g,logPartition n β g ∂couplingLaw n)/(n : ℝ)
def freeEnergyVariance (n : ℕ) (β : ℝ) : ℝ := variance (logPartition n β) (couplingLaw n)
def groundStateVariance (n : ℕ) : ℝ := variance (groundState n) (couplingLaw n)
def groundMean (n : ℕ) : ℝ := (∫ g,groundState n g ∂couplingLaw n)/(n : ℝ)

/-- The independent common completion D has variance exactly one half. -/
def completionLaw (n : ℕ) : Measure (Couplings n × ℝ) :=
  (couplingLaw n).prod (gaussianReal 0 (1/2))
def diagonalNoise (n : ℕ) (p : Couplings n × ℝ) : ℝ := p.2
def completedLogPartition (n : ℕ) (β : ℝ) (p : Couplings n × ℝ) : ℝ :=
  logPartition n β p.1+β*p.2
def completedGroundState (n : ℕ) (p : Couplings n × ℝ) : ℝ := groundState n p.1+p.2

def centeredCGF (n : ℕ) (β s : ℝ) : ℝ :=
  cgf (fun g => logPartition n β g-∫ z,logPartition n β z ∂couplingLaw n) (couplingLaw n) s

def completedFractionalPressure (n : ℕ) (β s : ℝ) : ℝ :=
  if s = 0 then pressure n β else cgf (completedLogPartition n β) (completionLaw n) s/((n : ℝ)*s)
def completedGroundLaplace (n : ℕ) (lam : ℝ) : ℝ :=
  if lam = 0 then groundMean n else cgf (completedGroundState n) (completionLaw n) lam/((n : ℝ)*lam)

def couplingEnvelope (n : ℕ) (g : Couplings n) : ℝ :=
  (1/Real.sqrt (n : ℝ))*∑ e : Edge n,|g e|

instance completionLaw_probability (n : ℕ) : IsProbabilityMeasure (completionLaw n) := by
  unfold completionLaw
  infer_instance

theorem energy_parameter (n : ℕ) (β : ℝ) (g : Couplings n) (σ : Configuration n) :
    Paper.skHamiltonian β 0 g σ = β*energy n g σ := by
  unfold energy Paper.skHamiltonian
  ring

theorem couplingEnvelope_nonneg (n : ℕ) (g : Couplings n) : 0 ≤ couplingEnvelope n g := by
  unfold couplingEnvelope
  positivity

theorem abs_energy_le_envelope (n : ℕ) (g : Couplings n) (σ : Configuration n) :
    |energy n g σ| ≤ couplingEnvelope n g := by
  have habs (e : Edge n) :
      |g e*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)| = |g e| := by
    cases σ e.val.1 <;> cases σ e.val.2 <;> simp [Paper.spinSign]
  unfold energy Paper.skHamiltonian couplingEnvelope
  simp only [zero_mul,add_zero,abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1/Real.sqrt (n : ℝ))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp_rw [habs])

theorem energy_le_groundState (n : ℕ) (g : Couplings n) (σ : Configuration n) :
    energy n g σ ≤ groundState n g := Finset.le_sup' _ (Finset.mem_univ σ)

theorem abs_groundState_le_envelope (n : ℕ) (g : Couplings n) :
    |groundState n g| ≤ couplingEnvelope n g := by
  obtain ⟨σ,hσ,hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Configuration n)).Nonempty) (energy n g)
  change |Finset.univ.sup' Finset.univ_nonempty (energy n g)| ≤ _
  rw [hmax]
  exact abs_energy_le_envelope n g σ

theorem continuous_groundState (n : ℕ) : Continuous (groundState n) := by
  have hc : Continuous (Finset.univ.sup' Finset.univ_nonempty (fun σ : Configuration n => fun g : Couplings n => energy n g σ)) :=
    Finset.sup'_induction (s := Finset.univ) (H := Finset.univ_nonempty)
      (f := fun σ : Configuration n => fun g : Couplings n => energy n g σ) (p := fun f => Continuous f)
      (fun _ hf _ hg => hf.sup hg) (fun σ _ => Paper.continuous_skHamiltonian 1 0 σ)
  have heq : groundState n = Finset.univ.sup' Finset.univ_nonempty (fun σ : Configuration n => fun g : Couplings n => energy n g σ) := by
    funext g
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun σ : Configuration n => fun z : Couplings n => energy n z σ) g).symm
  rw [heq]
  exact hc

theorem continuous_logPartition (n : ℕ) (β : ℝ) : Continuous (logPartition n β) :=
  (Paper.continuous_skPartitionFunction β 0).log (fun g => (Paper.skPartitionFunction_pos β 0 g).ne')

theorem configuration_card (n : ℕ) : Fintype.card (Configuration n) = 2^n := by
  simp [Configuration,Paper.SKConfiguration]

/-- The exact deterministic soft maximum comparison, including N log 2. -/
theorem logPartition_soft_max (n : ℕ) (β : ℝ) (hβ : 0 < β) (g : Couplings n) :
    β*groundState n g ≤ logPartition n β g ∧
    logPartition n β g ≤ β*groundState n g+(n : ℝ)*Real.log 2 := by
  obtain ⟨σ,hσ,hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Configuration n)).Nonempty) (energy n g)
  constructor
  · have hh := Paper.skHamiltonian_le_log_partition β 0 g σ
    rw [energy_parameter] at hh
    change β*(Finset.univ.sup' Finset.univ_nonempty (energy n g)) ≤ _
    rw [hmax]
    exact hh
  · have hsum : Paper.skPartitionFunction β 0 g ≤
        (Fintype.card (Configuration n) : ℝ)*Real.exp (β*groundState n g) := by
      unfold Paper.skPartitionFunction
      calc
        _ ≤ ∑ _σ : Configuration n,Real.exp (β*groundState n g) :=
          Finset.sum_le_sum fun σ _ => Real.exp_le_exp.mpr (by
            rw [energy_parameter]
            exact mul_le_mul_of_nonneg_left (energy_le_groundState n g σ) hβ.le)
        _ = _ := by simp
    have hh := Real.log_le_log (Paper.skPartitionFunction_pos β 0 g) hsum
    rw [configuration_card, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_mul (by positivity : (2:ℝ)^n ≠ 0) (Real.exp_ne_zero _),
      Real.log_pow,Real.log_exp] at hh
    unfold logPartition
    linarith

/-- Energy-normalized soft maximum; this is the pointwise zero-temperature passage. -/
theorem energyFreeEnergy_sub_groundState (n : ℕ) (β : ℝ) (hβ : 0 < β) (g : Couplings n) :
    0 ≤ energyFreeEnergy n β g-groundState n g ∧
    energyFreeEnergy n β g-groundState n g ≤ (n : ℝ)*Real.log 2/β := by
  obtain ⟨hl,hu⟩ := logPartition_soft_max n β hβ g
  unfold energyFreeEnergy
  constructor
  · apply sub_nonneg.mpr
    exact (le_div_iff₀ hβ).mpr (by nlinarith)
  · apply (le_div_iff₀ hβ).mpr
    rw [sub_mul,div_mul_cancel₀ _ hβ.ne']
    nlinarith

theorem continuous_couplingEnvelope (n : ℕ) : Continuous (couplingEnvelope n) := by
  unfold couplingEnvelope
  fun_prop

/-- A pathwise affine absolute bound for every real inverse temperature. -/
theorem abs_logPartition_le_envelope (n : ℕ) (β : ℝ) (g : Couplings n) :
    |logPartition n β g| ≤ (n : ℝ)*Real.log 2+|β| * couplingEnvelope n g := by
  have henv := couplingEnvelope_nonneg n g
  have hh (σ : Configuration n) : |Paper.skHamiltonian β 0 g σ| ≤ |β| * couplingEnvelope n g := by
    rw [energy_parameter,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_energy_le_envelope n g σ) (abs_nonneg β)
  have hsum : Paper.skPartitionFunction β 0 g ≤
      (Fintype.card (Configuration n) : ℝ)*Real.exp (|β| * couplingEnvelope n g) := by
    unfold Paper.skPartitionFunction
    calc
      _ ≤ ∑ _σ : Configuration n,Real.exp (|β| * couplingEnvelope n g) :=
        Finset.sum_le_sum fun σ _ => Real.exp_le_exp.mpr ((le_abs_self _).trans (hh σ))
      _ = _ := by simp
  have hu := Real.log_le_log (Paper.skPartitionFunction_pos β 0 g) hsum
  rw [configuration_card,Nat.cast_pow,Nat.cast_ofNat,
    Real.log_mul (by positivity : (2:ℝ)^n ≠ 0) (Real.exp_ne_zero _),
    Real.log_pow,Real.log_exp] at hu
  have hl := Paper.skHamiltonian_le_log_partition β 0 g (fun _ => true)
  have hab := (abs_le.mp (hh (fun _ => true))).1
  have hnlog : 0 ≤ (n : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  exact abs_le.mpr ⟨by change _ ≤ Real.log _; linarith,by change Real.log _ ≤ _; linarith⟩

theorem integrable_couplingEnvelope (n : ℕ) : Integrable (couplingEnvelope n) (couplingLaw n) := by
  unfold couplingEnvelope
  apply Integrable.const_mul
  exact integrable_finsetSum _ fun e _ => (Paper.integrable_skCoupling_coordinate e).abs

/-- Gaussian domination genuinely supplies every exponential moment. -/
theorem integrable_exp_couplingEnvelope (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun g => Real.exp (c*couplingEnvelope n g)) (couplingLaw n) := by
  have hprod : Integrable (fun g : Couplings n =>
      ∏ e : Edge n,Real.exp ((c/Real.sqrt (n : ℝ))*|g e|)) (couplingLaw n) :=
    Integrable.fintype_prod fun e => FRSB.integrable_exp_mul_abs_gaussian 0
      (c/Real.sqrt (n : ℝ)) 1 (by positivity)
  have heq : (fun g : Couplings n => Real.exp (c*couplingEnvelope n g)) =
      fun g => ∏ e : Edge n,Real.exp ((c/Real.sqrt (n : ℝ))*|g e|) := by
    funext g
    unfold couplingEnvelope
    rw [←Real.exp_sum,←Finset.mul_sum]
    congr 1
    ring
  rw [heq]
  exact hprod

theorem integrable_exp_logPartition (n : ℕ) (β a : ℝ) :
    Integrable (fun g => Real.exp (a*logPartition n β g)) (couplingLaw n) := by
  have hdom := (integrable_exp_couplingEnvelope n (|a| * |β|) (by positivity)).const_mul
    (Real.exp (|a| * ((n : ℝ)*Real.log 2)))
  apply hdom.mono' ((continuous_logPartition n β).const_mul a |>.rexp |>.aestronglyMeasurable)
  apply Eventually.of_forall
  intro g
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : a*logPartition n β g ≤ |a| * ((n : ℝ)*Real.log 2+|β| * couplingEnvelope n g) := by
    calc
      _ ≤ |a*logPartition n β g| := le_abs_self _
      _ = |a| * |logPartition n β g| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_logPartition_le_envelope n β g) (abs_nonneg a)
  nlinarith

theorem integrable_exp_groundState (n : ℕ) (a : ℝ) :
    Integrable (fun g => Real.exp (a*groundState n g)) (couplingLaw n) := by
  apply (integrable_exp_couplingEnvelope n |a| (abs_nonneg _)).mono'
    ((continuous_groundState n).const_mul a |>.rexp |>.aestronglyMeasurable)
  apply Eventually.of_forall
  intro g
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |a*groundState n g| := le_abs_self _
    _ = |a| * |groundState n g| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_groundState_le_envelope n g) (abs_nonneg _)

theorem integrable_logPartition (n : ℕ) (β : ℝ) :
    Integrable (logPartition n β) (couplingLaw n) := Paper.integrable_log_skPartitionFunction β 0

theorem integrable_energyFreeEnergy (n : ℕ) (β : ℝ) :
    Integrable (energyFreeEnergy n β) (couplingLaw n) := (integrable_logPartition n β).div_const β

theorem integrable_groundState (n : ℕ) : Integrable (groundState n) (couplingLaw n) := by
  exact (integrable_couplingEnvelope n).mono' (continuous_groundState n).aestronglyMeasurable
    (.of_forall fun g => by rw [Real.norm_eq_abs]; exact abs_groundState_le_envelope n g)

theorem integrable_pow_abs_logPartition (n : ℕ) (β : ℝ) (p : ℕ) :
    Integrable (fun g => |logPartition n β g|^p) (couplingLaw n) :=
  integrable_pow_abs_of_integrable_exp_mul one_ne_zero
    (integrable_exp_logPartition n β 1) (integrable_exp_logPartition n β (-1)) p

theorem integrable_pow_abs_groundState (n : ℕ) (p : ℕ) :
    Integrable (fun g => |groundState n g|^p) (couplingLaw n) :=
  integrable_pow_abs_of_integrable_exp_mul one_ne_zero
    (integrable_exp_groundState n 1) (integrable_exp_groundState n (-1)) p

theorem memLp_two_logPartition (n : ℕ) (β : ℝ) : MemLp (logPartition n β) 2 (couplingLaw n) := by
  apply (memLp_two_iff_integrable_sq (continuous_logPartition n β).aestronglyMeasurable).mpr
  simpa only [sq_abs] using integrable_pow_abs_logPartition n β 2

theorem memLp_two_groundState (n : ℕ) : MemLp (groundState n) 2 (couplingLaw n) := by
  apply (memLp_two_iff_integrable_sq (continuous_groundState n).aestronglyMeasurable).mpr
  simpa only [sq_abs] using integrable_pow_abs_groundState n 2

theorem pressure_eq_finiteSKFreeEnergy (n : ℕ) (β : ℝ) :
    pressure n β = Paper.finiteSKFreeEnergy β 0 n := by
  unfold pressure Paper.finiteSKFreeEnergy logPartition
  ring

end QuantitativePaper
