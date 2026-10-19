module

public import SphericalAging.ParameterizedItoLift
public import SphericalAging.PredictableItoTime

public section

/-! The actual continuous Itô versions of independent-background families
have the genuine base Itô versions as almost every parameter section.
This follows from the proved operator identity and genuine time restriction.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ParameterizedItoVersion
open HardSphereDynamics VectorIto IndependentBackgroundDriver ParameterizedItoLift PredictableItoTime
open FourPapersCommon.FilteredBrownian
variable {A Ω : Type*} [mA : MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℕ}
set_option maxHeartbeats 1800000

/-- A terminal actual continuous Itô version is identified with its true
parameterwise terminal version, in the actual enlarged filtration. -/
theorem itoVersion_familyLift_slice (D : BrownianDriver N P F) (i : Fin N)
    (f : Lp (PredictableProcessL2 F P) 2 ρ) (t : ℝ≥0) :
    ∀ᵐ a ∂ρ, (fun ω => itoVersion ((driver (ρ := ρ) D).brownian i)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable i) ((driver (ρ := ρ) D).filtered i)
      (PredictableFamilyLift.familyLift f) t (a,ω)) =ᵐ[P]
      itoVersion (D.brownian i) (D.coordinateStronglyMeasurable i) (D.filtered i) (f a) t := by
  let fcut := (FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t).compLpL 2 ρ f
  have hproc : naturalItoProcess ((driver (ρ := ρ) D).filtered i).toIsPreBrownianReal
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable i) ((driver (ρ := ρ) D).filtered i)
      (PredictableFamilyLift.familyLift f) t =
      coordinateIto (driver (ρ := ρ) D) i (PredictableFamilyLift.familyLift fcut) := by
    unfold FourPapersCommon.FilteredBrownian.naturalItoProcess
    rw [predictableTimeRestrict_familyLift]
    rfl
  have hver := Measure.ae_ae_of_ae_prod (itoVersion_ae_eq ((driver (ρ := ρ) D).brownian i)
    ((driver (ρ := ρ) D).coordinateStronglyMeasurable i) ((driver (ρ := ρ) D).filtered i)
    (PredictableFamilyLift.familyLift f) t)
  filter_upwards [hver,coordinateIto_familyLift_slice D i fcut,
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t).coeFn_compLpL f] with a ha hb hc
  have hs : coordinateIto D i (fcut a) = naturalItoProcess (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) (f a) t := by
    change coordinateIto D i
      (((FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t).compLpL 2 ρ f) a) = _
    rw [hc]
    rfl
  filter_upwards [ha,hb,itoVersion_ae_eq (D.brownian i) (D.coordinateStronglyMeasurable i)
    (D.filtered i) (f a) t] with ω ha hb hbase
  rw [← ha,hproc,hb,hs]
  exact hbase

end SphericalAging.ParameterizedItoVersion
