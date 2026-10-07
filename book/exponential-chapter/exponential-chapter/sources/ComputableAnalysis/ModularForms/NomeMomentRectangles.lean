import ComputableAnalysis.ModularForms.RepresentedDoublePrefixes
import ComputableAnalysis.ModularForms.NomePowerComposition
import ComputableAnalysis.ModularForms.NomeMomentPrefixLinearity
import ComputableAnalysis.ModularForms.LambertPositivePowers

/-! Exact finite rectangles beneath the moment-to-Lambert comparison. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Actual moment rectangles equal weighted positive geometric rectangles after
exchanging their finite rows and columns. No infinite rearrangement is assumed. -/
theorem polynomialNomeMomentPrefix_rectangle (z : Scalar) (k N M : Nat) :
    (ScalarSeries.block (fun n => polynomialNomeMomentPrefix (nomePowerScalar z n) k M) 0 N).Equiv
      (ScalarSeries.block (fun m => scaleRat (((m+1:Nat):Rat)^k)
        (lambertPositivePrefix (nomePowerScalar z m) N)) 0 M) := by
  let t := fun n m => polynomialNomeMomentTerm (nomePowerScalar z n) k m
  let u := fun m n => scaleRat (((m+1:Nat):Rat)^k)
    (LocalODE.power (nomePowerScalar z m).val (n+1))
  have ht n m : (t n m).Valid := polynomialNomeMomentTerm_valid _ k m
  have hu m n : (u m n).Valid := scaleRat_valid (LocalODE.power_valid _ (nomePowerScalar z m).property (n+1))
  have he m n : (t n m).Equiv (u m n) := scaleRat_equiv (nomePowerScalar_power_comm z n m)
  have hc m := ScalarSeries.block_congr (fun n => t n m) (u m) (he m) 0 N
  have hs m := representedBlock_scale
    (fun n => LocalODE.power (nomePowerScalar z m).val (n+1))
    (fun n => LocalODE.power_valid _ (nomePowerScalar z m).property (n+1))
    (((m+1:Nat):Rat)^k) 0 N
  have hshift m : ScalarSeries.block (fun n => LocalODE.power (nomePowerScalar z m).val (n+1)) 0 N=
      lambertPositivePrefix (nomePowerScalar z m) N := by
    unfold lambertPositivePrefix
    rw [representedBlock_shift (LocalODE.power (nomePowerScalar z m).val) 1 N]
    simp only [Nat.add_comm 1]
  have hf m : (ScalarSeries.block (fun n => t n m) 0 N).Equiv
      (scaleRat (((m+1:Nat):Rat)^k) (lambertPositivePrefix (nomePowerScalar z m) N)) := by
    have hs := hs m
    rw [hshift m] at hs
    exact equiv_trans (ScalarSeries.block_valid _ (fun n => ht n m) 0 N)
      (ScalarSeries.block_valid _ (hu m) 0 N)
      (scaleRat_valid (lambertPositivePrefix_valid _ N)) (hc m) hs
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => polynomialNomeMomentPrefix_valid _ k M) 0 N)
    (ScalarSeries.block_valid _ (fun m => ScalarSeries.block_valid _ (fun n => ht n m) 0 N) 0 M)
    (ScalarSeries.block_valid _ (fun m => scaleRat_valid (lambertPositivePrefix_valid _ N)) 0 M)
    (representedDoublePrefix_transpose t ht N M)
    (ScalarSeries.block_congr _ _ hf 0 M)

end ComputableAnalysis.ModularForms
