module
public import OverlapPaper.BlockCovariance
public import OverlapPaper.FiniteMoments

@[expose] public section

/-! The independent physical block realization and its exact mixed covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OverlapPaper
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

def blockDisorderLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (n m : ℕ) :
    Measure (Disorder (n + m)) :=
  ((disorderLaw ξ n).prod (disorderLaw ξ m)).map (blockHamiltonianCLM n m)

instance blockDisorderLaw_probability (ξ : FourPapersCommon.AdmissibleEvenMixture) (n m : ℕ) :
    IsProbabilityMeasure (blockDisorderLaw ξ n m) := by
  unfold blockDisorderLaw
  infer_instance

instance blockDisorderLaw_gaussian (ξ : FourPapersCommon.AdmissibleEvenMixture) (n m : ℕ) :
    IsGaussian (blockDisorderLaw ξ n m) := by
  unfold blockDisorderLaw
  infer_instance

theorem integral_blockDisorder_eq_zero (ξ : FourPapersCommon.AdmissibleEvenMixture) (n m : ℕ) :
    (∫ g : Disorder (n + m), g ∂blockDisorderLaw ξ n m) = 0 := by
  let P := (disorderLaw ξ n).prod (disorderLaw ξ m)
  have hfst : HasLaw (Prod.fst : Disorder n × Disorder m → Disorder n) (disorderLaw ξ n) P :=
    measurePreserving_fst.hasLaw
  have hsnd : HasLaw (Prod.snd : Disorder n × Disorder m → Disorder m) (disorderLaw ξ m) P :=
    measurePreserving_snd.hasLaw
  have hp0 : (∫ g : Disorder n × Disorder m, g ∂P) = 0 := by
    have hpint : Integrable (id : Disorder n × Disorder m → Disorder n × Disorder m) P :=
      IsGaussian.integrable_id
    apply Prod.ext
    · change (∫ g, id g ∂P).1 = 0
      rw [fst_integral hpint]
      exact (hfst.integral_comp aestronglyMeasurable_id).trans (integral_disorder_eq_zero ξ n)
    · change (∫ g, id g ∂P).2 = 0
      rw [snd_integral hpint]
      exact (hsnd.integral_comp aestronglyMeasurable_id).trans (integral_disorder_eq_zero ξ m)
  unfold blockDisorderLaw
  change (∫ g, id g ∂P.map (blockHamiltonianCLM n m)) = 0
  rw [integral_map_of_stronglyMeasurable (blockHamiltonianCLM n m).continuous.measurable
    stronglyMeasurable_id]
  change (∫ g, blockHamiltonianCLM n m (id g) ∂P) = 0
  rw [(blockHamiltonianCLM n m).integral_comp_comm (IsGaussian.integrable_id (μ := P))]
  simp only [id_eq] at *
  rw [hp0]
  exact map_zero _

theorem integral_blockDisorder_product (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (n m : ℕ) (σ τ : Configuration (n + m)) :
    (∫ g : Disorder (n + m), g σ * g τ ∂blockDisorderLaw ξ n m) =
      blockCovariance ξ n m σ τ := by
  let P := (disorderLaw ξ n).prod (disorderLaw ξ m)
  let a := SpinGlass.cfgLeft (N := n) (M := m) σ
  let a' := SpinGlass.cfgLeft (N := n) (M := m) τ
  let b := SpinGlass.cfgRight (N := n) (M := m) σ
  let b' := SpinGlass.cfgRight (N := n) (M := m) τ
  let F (ρ : Configuration n) (g : Disorder n × Disorder m) : ℝ := g.1 ρ
  let S (ρ : Configuration m) (g : Disorder n × Disorder m) : ℝ := g.2 ρ
  have hfst : HasLaw (Prod.fst : Disorder n × Disorder m → Disorder n) (disorderLaw ξ n) P :=
    measurePreserving_fst.hasLaw
  have hsnd : HasLaw (Prod.snd : Disorder n × Disorder m → Disorder m) (disorderLaw ξ m) P :=
    measurePreserving_snd.hasLaw
  have hF (ρ : Configuration n) : MemLp (F ρ) 2 P :=
    (hfst.hasGaussianLaw.map_fun (PiLp.proj 2 (fun _ : Configuration n => ℝ) ρ)).memLp_two
  have hS (ρ : Configuration m) : MemLp (S ρ) 2 P :=
    (hsnd.hasGaussianLaw.map_fun (PiLp.proj 2 (fun _ : Configuration m => ℝ) ρ)).memLp_two
  have hFF : (∫ g, F a g * F a' g ∂P) = finiteCovariance ξ n a a' := by
    have hi := hfst.integral_comp (f := fun g : Disorder n => g a * g a') (by fun_prop)
    exact hi.trans (integral_hamiltonian_product ξ a a')
  have hSS : (∫ g, S b g * S b' g ∂P) = finiteCovariance ξ m b b' := by
    have hi := hsnd.integral_comp (f := fun g : Disorder m => g b * g b') (by fun_prop)
    exact hi.trans (integral_hamiltonian_product ξ b b')
  have hFS (ρ : Configuration n) (θ : Configuration m) : (∫ g, F ρ g * S θ g ∂P) = 0 := by
    have hi := indepFun_prod (μ := disorderLaw ξ n) (ν := disorderLaw ξ m)
      (show Measurable (fun g : Disorder n => g ρ) by fun_prop)
      (show Measurable (fun g : Disorder m => g θ) by fun_prop)
    have hh := hi.integral_mul_eq_mul_integral (hF ρ).aestronglyMeasurable (hS θ).aestronglyMeasurable
    have hmF : (∫ g, F ρ g ∂P) = 0 :=
      (hfst.integral_comp (f := fun g : Disorder n => g ρ) (by fun_prop)).trans (integral_hamiltonian ξ ρ)
    have hmS : (∫ g, S θ g ∂P) = 0 :=
      (hsnd.integral_comp (f := fun g : Disorder m => g θ) (by fun_prop)).trans (integral_hamiltonian ξ θ)
    change (∫ g, F ρ g * S θ g ∂P) = (∫ g, F ρ g ∂P) * (∫ g, S θ g ∂P) at hh
    simpa only [hmF, hmS, zero_mul] using hh
  have hSF : (∫ g, S b g * F a' g ∂P) = 0 := by
    simpa only [mul_comm] using hFS a' b
  unfold blockDisorderLaw
  rw [integral_map_of_stronglyMeasurable (blockHamiltonianCLM n m).continuous.measurable
    (f := fun g : Disorder (n + m) => g σ * g τ) (by fun_prop)]
  change (∫ g, (F a g + S b g) * (F a' g + S b' g) ∂P) = _
  simp_rw [add_mul, mul_add]
  have hFFint := (hF a).integrable_mul (hF a')
  have hFSint := (hF a).integrable_mul (hS b')
  have hSFint := (hS b).integrable_mul (hF a')
  have hSSint := (hS b).integrable_mul (hS b')
  change Integrable (fun g => F a g * F a' g) P at hFFint
  change Integrable (fun g => F a g * S b' g) P at hFSint
  change Integrable (fun g => S b g * F a' g) P at hSFint
  change Integrable (fun g => S b g * S b' g) P at hSSint
  calc
    (∫ g, F a g * F a' g + F a g * S b' g + (S b g * F a' g + S b g * S b' g) ∂P) =
        (∫ g, F a g * F a' g + F a g * S b' g ∂P) +
          ∫ g, S b g * F a' g + S b g * S b' g ∂P := by
      simpa only [Pi.add_apply] using! integral_add (hFFint.add hFSint) (hSFint.add hSSint)
    _ = ((∫ g, F a g * F a' g ∂P) + (∫ g, F a g * S b' g ∂P)) +
        ((∫ g, S b g * F a' g ∂P) + (∫ g, S b g * S b' g ∂P)) := by
      exact congrArg₂ HAdd.hAdd (integral_add hFFint hFSint) (integral_add hSFint hSSint)
    _ = blockCovariance ξ n m σ τ := by
      rw [hFF, hSS, hFS, hSF]
      simp only [add_zero, zero_add]
      rfl

end OverlapPaper
