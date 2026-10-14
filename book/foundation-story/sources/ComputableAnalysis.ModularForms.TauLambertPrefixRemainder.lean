import ComputableAnalysis.ModularForms.TauLambertRemainderSum

/-! Exact finite-prefix and term-remainder agreement. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem remainder_add (F G D f g d h : Scalar) :
    (SeriesLimitLaws.remainder (add F.val f.val) (add G.val g.val) (add D.val d.val) h.val).Equiv
      (add (SeriesLimitLaws.remainder F.val G.val D.val h.val)
        (SeriesLimitLaws.remainder f.val g.val d.val h.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := SeriesLimitLaws.remainder_valid _ _ _ _ (add_valid F.property f.property)
      (add_valid G.property g.property) (add_valid D.property d.property) h.property)
    (hright := add_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property h.property)
      (SeriesLimitLaws.remainder_valid _ _ _ _ f.property g.property d.property h.property))
  let X := ComplexRawQuotient.ofRaw F.val F.property
  let Y := ComplexRawQuotient.ofRaw G.val G.property
  let Z := ComplexRawQuotient.ofRaw D.val D.property
  let x := ComplexRawQuotient.ofRaw f.val f.property
  let y := ComplexRawQuotient.ofRaw g.val g.property
  let z := ComplexRawQuotient.ofRaw d.val d.property
  let H := ComplexRawQuotient.ofRaw h.val h.property
  change ((X+x)-(Y+y))-(Z+z)*H=((X-Y)-Z*H)+((x-y)-z*H)
  grind only

private theorem block_remainder (f g d : Nat → Scalar) (h : Scalar) (N : Nat) :
    (SeriesLimitLaws.remainder (ScalarSeries.block (fun n => (f n).val) 0 N)
      (ScalarSeries.block (fun n => (g n).val) 0 N)
      (ScalarSeries.block (fun n => (d n).val) 0 N) h.val).Equiv
      (ScalarSeries.block (fun n => SeriesLimitLaws.remainder (f n).val (g n).val (d n).val h.val) 0 N) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := SeriesLimitLaws.remainder_valid _ _ _ _ (ofQComplex_valid _) (ofQComplex_valid _) (ofQComplex_valid _) h.property)
      (hright := ofQComplex_valid _)
    let H := ComplexRawQuotient.ofRaw h.val h.property
    change (0-0)-0*H=0
    grind only
  | succ N ih =>
    let F : Scalar := ⟨ScalarSeries.block (fun n => (f n).val) 0 N, ScalarSeries.block_valid _ (fun n => (f n).property) 0 N⟩
    let G : Scalar := ⟨ScalarSeries.block (fun n => (g n).val) 0 N, ScalarSeries.block_valid _ (fun n => (g n).property) 0 N⟩
    let D : Scalar := ⟨ScalarSeries.block (fun n => (d n).val) 0 N, ScalarSeries.block_valid _ (fun n => (d n).property) 0 N⟩
    simp only [ScalarSeries.block, Nat.zero_add]
    exact equiv_trans
      (SeriesLimitLaws.remainder_valid _ _ _ _ (add_valid F.property (f N).property)
        (add_valid G.property (g N).property) (add_valid D.property (d N).property) h.property)
      (add_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property h.property)
        (SeriesLimitLaws.remainder_valid _ _ _ _ (f N).property (g N).property (d N).property h.property))
      (add_valid (ScalarSeries.block_valid _ (fun n => SeriesLimitLaws.remainder_valid _ _ _ _ (f n).property (g n).property (d n).property h.property) 0 N)
        (SeriesLimitLaws.remainder_valid _ _ _ _ (f N).property (g N).property (d N).property h.property))
      (remainder_add F G D (f N) (g N) (d N) h)
      (add_equiv ih (equiv_refl _ (SeriesLimitLaws.remainder_valid _ _ _ _ (f N).property (g N).property (d N).property h.property)))

/-- The actual prefix remainder is exactly the finite block of actual term remainders. -/
theorem tauLambertPrefix_remainder_block (a z : Scalar) (ha : tauEulerNomeDomain a)
    (hz : tauEulerNomeDomain z) (N : Nat) :
    (SeriesLimitLaws.remainder ((tauLambertPrefixMap 1 N).eval z hz).val
      ((tauLambertPrefixMap 1 N).eval a ha).val
      ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).val (sub z.val a.val)).Equiv
      (ScalarSeries.block (fun n => (tauLambertTermRemainder a z ha hz n).val) 0 N) := by
  let F := (tauLambertPrefixMap 1 N).eval z hz
  let G := (tauLambertPrefixMap 1 N).eval a ha
  let D := (tauLambertPrefixMap_holomorphic 1 N).derivative a ha
  let B : Scalar := ⟨ScalarSeries.block (fun n => ((tauWeightedLambertMap_holomorphic 1 n).derivative a ha).val) 0 N,
    ScalarSeries.block_valid _ (fun n => ((tauWeightedLambertMap_holomorphic 1 n).derivative a ha).property) 0 N⟩
  let H : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have he := FunctionTheory.sub_congr (equiv_refl (sub F.val G.val) (sub_valid F.property G.property))
    (mul_equiv D.property B.property H.property H.property (tauLambertPrefixMap_derivative 1 N a ha) (equiv_refl _ H.property))
  exact equiv_trans (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property H.property)
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property B.property H.property)
    (ScalarSeries.block_valid _ (fun n => (tauLambertTermRemainder a z ha hz n).property) 0 N) he
    (block_remainder (fun n => (tauWeightedLambertMap 1 n).eval z hz)
      (fun n => (tauWeightedLambertMap 1 n).eval a ha)
      (fun n => (tauWeightedLambertMap_holomorphic 1 n).derivative a ha) H N)

end ComputableAnalysis.ModularForms
