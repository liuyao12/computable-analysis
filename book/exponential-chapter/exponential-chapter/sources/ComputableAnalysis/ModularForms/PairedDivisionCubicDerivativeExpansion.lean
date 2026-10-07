import ComputableAnalysis.ModularForms.PairedDivisionCubicDerivativePrefixes

/-! Cubic center expansion of the actual convergent derivative series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def difference (x y : Scalar) : Scalar := ⟨sub x.val y.val,sub_valid x.property y.property⟩
private def scale (r : Rat) (x : Scalar) : Scalar := ⟨scaleRat r x.val,scaleRat_valid x.property⟩

private theorem prefix_identity (t b d : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hb : ∀ n, (b n).Valid) (hd : ∀ n, (d n).Valid)
    (L K : Scalar) (N : Nat) :
    (ScalarSeries.block (fun n => sub (sub (t n) (mul L.val (b n))) (mul K.val (d n))) 0 N).Equiv
      (sub (sub (ScalarSeries.block t 0 N) (mul L.val (ScalarSeries.block b 0 N)))
        (mul K.val (ScalarSeries.block d 0 N))) := by
  let u := fun n => sub (t n) (mul L.val (b n))
  have hu n : (u n).Valid := sub_valid (ht n) (mul_valid L.property (hb n))
  have h1 := representedBlock_sub u (fun n => mul K.val (d n)) hu
    (fun n => mul_valid K.property (hd n)) 0 N
  have h2 := FunctionTheory.sub_congr (representedBlock_sub t (fun n => mul L.val (b n)) ht
    (fun n => mul_valid L.property (hb n)) 0 N) (representedPrefix_mul_left d hd K N)
  have h3 := FunctionTheory.sub_congr
    (FunctionTheory.sub_congr (equiv_refl _ (ScalarSeries.block_valid t ht 0 N))
      (representedPrefix_mul_left b hb L N))
    (equiv_refl _ (mul_valid K.property (ScalarSeries.block_valid d hd 0 N)))
  exact equiv_trans (ScalarSeries.block_valid _ (fun n => sub_valid (hu n) (mul_valid K.property (hd n))) 0 N)
    (sub_valid (ScalarSeries.block_valid u hu 0 N)
      (ScalarSeries.block_valid _ (fun n => mul_valid K.property (hd n)) 0 N))
    (sub_valid (sub_valid (ScalarSeries.block_valid t ht 0 N) (mul_valid L.property (ScalarSeries.block_valid b hb 0 N)))
      (mul_valid K.property (ScalarSeries.block_valid d hd 0 N))) h1
    (equiv_trans
      (sub_valid (ScalarSeries.block_valid u hu 0 N)
        (ScalarSeries.block_valid _ (fun n => mul_valid K.property (hd n)) 0 N))
      (sub_valid (sub_valid (ScalarSeries.block_valid t ht 0 N)
        (ScalarSeries.block_valid _ (fun n => mul_valid L.property (hb n)) 0 N))
        (mul_valid K.property (ScalarSeries.block_valid d hd 0 N)))
      (sub_valid (sub_valid (ScalarSeries.block_valid t ht 0 N) (mul_valid L.property (ScalarSeries.block_valid b hb 0 N)))
        (mul_valid K.property (ScalarSeries.block_valid d hd 0 N))) h2 h3)

/-- The actual derivative series has its cubic center polynomial with an explicit fifth-order error. -/
theorem pairedRegularDivisionDerivativeValue_cubic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (sub (pairedRegularDivisionDerivativeValue z hz)
      (mul (scaleRat 2 z.val) pairedCenterQuadraticSum))
      (mul (scaleRat 4 (mul (mul z.val z.val) z.val)) pairedCenterQuarticSum))
      (47104*R*R*R*R*R) := by
  let Q : Scalar := ⟨pairedRegularDivisionDerivativeValue z hz,pairedRegularDivisionDerivativeValue_valid z hz⟩
  let B : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let D : Scalar := ⟨pairedCenterQuarticSum,pairedCenterQuarticSum_valid⟩
  let L := scale 2 z
  let K := scale 4 (scalarProduct (scalarProduct z z) z)
  let t := fun n => (pairedRegularDivisionDerivativeTerm z hz n).val
  have ht n : (t n).Valid := (pairedRegularDivisionDerivativeTerm z hz n).property
  let q := fun N => (⟨ScalarSeries.block t 0 (N+1),ScalarSeries.block_valid t ht 0 (N+1)⟩ : Scalar)
  let b := fun N => (⟨ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1)⟩ : Scalar)
  let d := fun N => (⟨ScalarSeries.block pairedCenterQuarticTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterQuarticTerm_valid 0 (N+1)⟩ : Scalar)
  let F := difference Q (scalarProduct L B)
  let f := fun N => difference (q N) (scalarProduct L (b N))
  let target := difference F (scalarProduct K D)
  let p := fun N => (difference (f N) (scalarProduct K (d N))).val
  have vp N : (p N).Valid := (difference (f N) (scalarProduct K (d N))).property
  let ML := DomainFunctions.scalarBound L
  let MK := DomainFunctions.scalarBound K
  have hML : 0≤ML := Rat.le_of_lt (DomainFunctions.scalarBound_pos L)
  have hMK : 0≤MK := Rat.le_of_lt (DomainFunctions.scalarBound_pos K)
  let eQ := fun N : Nat => 64*((N+1:Nat):Rat)⁻¹
  let eB := fun N : Nat => 4*((N+1:Nat):Rat)⁻¹
  let eD := fun N : Nat => 8*((N+1:Nat):Rat)⁻¹
  let eF := fun N => eQ N+2*ML*eB N
  have heF : ShrinksToZero eF := RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 64)
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 4) (2*ML) (Rat.mul_nonneg (by decide +kernel) hML))
  have he := RepresentedCauchySum.sum_shrinks _ _ heF
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 8) (2*MK) (Rat.mul_nonneg (by decide +kernel) hMK))
  have hnonneg (N : Nat) (k : Rat) (hk : 0≤k) : 0≤k*((N+1:Nat):Rat)⁻¹ := by
    have hn : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
    exact Rat.mul_nonneg hk (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  apply SeriesLimitLaws.small_of_prefix_bound target.val target.property p vp
    (47104*R*R*R*R*R) (fun N => eF N+2*MK*eD N) he
  · intro N
    have h1 := representedFactor_difference_small L.val B.val (b N).val L.property B.property
      (b N).property ML (eB N) hML (hnonneg N 4 (by decide +kernel))
      (DomainFunctions.scalar_small L) (pairedCenterQuadraticSum_close N)
    have hf := represented_prefix_sub_close Q (scalarProduct L B) (q N) (scalarProduct L (b N)) _ _
      (pairedRegularDivisionDerivativeValue_close z hz N) h1
    have h2 := representedFactor_difference_small K.val D.val (d N).val K.property D.property
      (d N).property MK (eD N) hMK (hnonneg N 8 (by decide +kernel))
      (DomainFunctions.scalar_small K) (pairedCenterQuarticSum_close N)
    exact represented_prefix_sub_close F (scalarProduct K D) (f N) (scalarProduct K (d N)) _ _ hf h2
  · intro N
    let u := fun n => sub (sub (t n) (mul L.val (pairedCenterQuadraticTerm n)))
      (mul K.val (pairedCenterQuarticTerm n))
    have hu n : (u n).Valid := sub_valid (sub_valid (ht n) (mul_valid L.property (pairedCenterQuadraticTerm_valid n)))
      (mul_valid K.property (pairedCenterQuarticTerm_valid n))
    have hc n : (pairedDerivativeCubicCenterResidual z hz n).val.Equiv (u n) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := (pairedDerivativeCubicCenterResidual z hz n).property) (hright := hu n)
      let T := ComplexRawQuotient.ofRaw (t n) (ht n)
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      let BB := ComplexRawQuotient.ofRaw (pairedCenterQuadraticTerm n) (pairedCenterQuadraticTerm_valid n)
      let DD := ComplexRawQuotient.ofRaw (pairedCenterQuarticTerm n) (pairedCenterQuarticTerm_valid n)
      change (T-ComplexRawQuotient.scaleRat 2 (Z*BB))-ComplexRawQuotient.scaleRat 4 (((Z*Z)*Z)*DD)=
        (T-(ComplexRawQuotient.scaleRat 2 Z)*BB)-(ComplexRawQuotient.scaleRat 4 ((Z*Z)*Z))*DD
      rw [ComplexRawQuotient.scaleRat_mul,ComplexRawQuotient.scaleRat_mul]
    have hpref := ScalarSeries.block_congr _ _ hc 0 (N+1)
    have hb := Small.congr
      (ScalarSeries.block_valid _ (fun n => (pairedDerivativeCubicCenterResidual z hz n).property) 0 (N+1))
      (ScalarSeries.block_valid u hu 0 (N+1)) hpref
      (pairedRegularDivisionDerivativePrefix_cubic_center_bound z hz (N+1) R hR hs)
    exact Small.congr (ScalarSeries.block_valid u hu 0 (N+1)) (vp N)
      (prefix_identity t pairedCenterQuadraticTerm pairedCenterQuarticTerm ht
        pairedCenterQuadraticTerm_valid pairedCenterQuarticTerm_valid L K (N+1)) hb

end ComputableAnalysis.ModularForms
