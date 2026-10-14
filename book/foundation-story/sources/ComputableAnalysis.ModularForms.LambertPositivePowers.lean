import ComputableAnalysis.ModularForms.LambertGeometricExpansion

/-! Literal positive-power prefixes of actual Lambert values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def lambertPositivePrefix (z : Scalar) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (LocalODE.power z.val) 1 N

theorem lambertPositivePrefix_valid (z : Scalar) (N : Nat) :
    (lambertPositivePrefix z N).Valid :=
  ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 1 N

theorem lambertGeometricPrefix_positive (z : Scalar) (N : Nat) :
    (lambertGeometricPrefix z N).Equiv (lambertPositivePrefix z N) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := lambertGeometricPrefix_valid z N) (hright := lambertPositivePrefix_valid z N)
  change ComplexRawQuotient.ofRaw (ScalarSeries.block (LocalODE.power z.val) 0 (N+1)) (ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 0 (N+1)) - 1 =
    ComplexRawQuotient.ofRaw (ScalarSeries.block (LocalODE.power z.val) 1 N) (ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 1 N)
  rw [ScalarSeries.prefix_image,ScalarSeries.block_image]
  let f := fun n => ComplexRawQuotient.ofRaw (LocalODE.power z.val n) (LocalODE.power_valid _ z.property n)
  have h := FiniteProducts.prefix_append f 1 N
  have hn : N+1=1+N := by omega
  rw [hn]
  change FiniteProducts.partialSum f (1+N)-1=FiniteProducts.block f 1 N
  rw [h]
  have h1 : FiniteProducts.partialSum f 1=1 := by
    change (0:ScalarAlgebra.Value)+1=1
    grind only
  rw [h1]
  grind only

theorem lambertPositivePrefix_close (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (lambertFactor z r) (lambertPositivePrefix z N)) (4*(2*r)^(N+1)) :=
  Small.congr
    (sub_valid (lambertFactor_valid z r hr hlocal hz) (lambertGeometricPrefix_valid z N))
    (sub_valid (lambertFactor_valid z r hr hlocal hz) (lambertPositivePrefix_valid z N))
    (FunctionTheory.sub_congr (equiv_refl _ (lambertFactor_valid z r hr hlocal hz))
      (lambertGeometricPrefix_positive z N))
    (lambertGeometricPrefix_close z r hr hlocal hz N)

theorem lambertPositiveTail_shrinks (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    ShrinksToZero (fun N => 4*(2*r)^(N+1)) :=
  SeriesLimitLaws.shrinks_shift _ (nomeGeometricTail_shrinks r hr hlocal) 1

end ComputableAnalysis.ModularForms
