import ComputableAnalysis.ModularForms.PairedDivisionQuadraticCoefficients

/-! Passing the actual quadratic center expansion through the regular-division series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem prefix_residual (t c b : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hc : ∀ n, (c n).Valid) (hb : ∀ n, (b n).Valid)
    (D : Scalar) (N : Nat) :
    (ScalarSeries.block (fun n => sub (sub (t n) (c n)) (mul D.val (b n))) 0 N).Equiv
      (sub (sub (ScalarSeries.block t 0 N) (ScalarSeries.block c 0 N))
        (mul D.val (ScalarSeries.block b 0 N))) := by
  have h1 := representedBlock_sub (fun n => sub (t n) (c n)) (fun n => mul D.val (b n))
    (fun n => sub_valid (ht n) (hc n)) (fun n => mul_valid D.property (hb n)) 0 N
  have h2 := FunctionTheory.sub_congr (representedBlock_sub t c ht hc 0 N)
    (representedPrefix_mul_left b hb D N)
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => sub_valid (sub_valid (ht n) (hc n)) (mul_valid D.property (hb n))) 0 N)
    (sub_valid (ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hc n)) 0 N)
      (ScalarSeries.block_valid _ (fun n => mul_valid D.property (hb n)) 0 N))
    (sub_valid (sub_valid (ScalarSeries.block_valid t ht 0 N) (ScalarSeries.block_valid c hc 0 N))
      (mul_valid D.property (ScalarSeries.block_valid b hb 0 N))) h1 h2

/-- The actual regular-division value has its constructed quadratic center
polynomial, with an explicit fourth-order error. -/
theorem pairedRegularDivisionValue_quadratic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (sub (pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz)) pairedCenterConstantSum)
      (mul (mul z.val z.val) pairedCenterQuadraticSum)) (1024*R*R*R*R) := by
  let hzz := LocalODE.interior_bound _ z hz
  let Q : Scalar := ⟨pairedRegularDivisionValue z hzz,pairedRegularDivisionValue_valid z hzz⟩
  let C : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let B : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let D : Scalar := ⟨mul z.val z.val,mul_valid z.property z.property⟩
  let t := fun n => (pairedRegularDivisionTerm z hzz n).val
  have ht n : (t n).Valid := (pairedRegularDivisionTerm z hzz n).property
  let q := fun N => (⟨ScalarSeries.block t 0 (N+1),ScalarSeries.block_valid t ht 0 (N+1)⟩ : Scalar)
  let c := fun N => (⟨ScalarSeries.block pairedCenterConstantTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterConstantTerm_valid 0 (N+1)⟩ : Scalar)
  let b := fun N => (⟨ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1)⟩ : Scalar)
  let p := fun N => sub (sub (q N).val (c N).val) (mul D.val (b N).val)
  have vp N : (p N).Valid := sub_valid (sub_valid (q N).property (c N).property)
    (mul_valid D.property (b N).property)
  let M := DomainFunctions.scalarBound D
  have hM : 0≤M := Rat.le_of_lt (DomainFunctions.scalarBound_pos D)
  let eQ := fun N : Nat => 8*((N+1:Nat):Rat)⁻¹
  let eC := fun N : Nat => 2*((N+1:Nat):Rat)⁻¹
  let eB := fun N : Nat => 4*((N+1:Nat):Rat)⁻¹
  have heQ : ShrinksToZero eQ := pairedReciprocalTail_shrinks 8
  have heC : ShrinksToZero eC := pairedReciprocalTail_shrinks 2
  have heB : ShrinksToZero eB := pairedReciprocalTail_shrinks 4
  have he := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ heQ heC)
    (SeriesLimitLaws.shrinks_scale _ heB (2*M) (Rat.mul_nonneg (by decide +kernel) hM))
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (sub_valid Q.property C.property) (mul_valid D.property B.property)) p vp
    (1024*R*R*R*R) (fun N => (eQ N+eC N)+2*M*eB N) he
  · intro N
    have h1 := represented_prefix_sub_close Q C (q N) (c N) _ _
      (pairedRegularDivisionValue_close z hzz N) (pairedCenterConstantSum_close N)
    have h0 : 0≤eB N := by
      have hn : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
      exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
    have h2 := representedFactor_difference_small D.val B.val (b N).val D.property B.property
      (b N).property M (eB N) hM h0 (DomainFunctions.scalar_small D) (pairedCenterQuadraticSum_close N)
    exact represented_prefix_sub_close
      ⟨sub Q.val C.val,sub_valid Q.property C.property⟩
      ⟨mul D.val B.val,mul_valid D.property B.property⟩
      ⟨sub (q N).val (c N).val,sub_valid (q N).property (c N).property⟩
      ⟨mul D.val (b N).val,mul_valid D.property (b N).property⟩ _ _ h1 h2
  · intro N
    have h := pairedRegularDivisionPrefix_quadratic_center_bound z hz (N+1) R hR hs
    exact Small.congr
      (ScalarSeries.block_valid _ (fun n => sub_valid (sub_valid (ht n) (pairedCenterConstantTerm_valid n))
        (mul_valid D.property (pairedCenterQuadraticTerm_valid n))) 0 (N+1)) (vp N)
      (prefix_residual t pairedCenterConstantTerm pairedCenterQuadraticTerm ht
        pairedCenterConstantTerm_valid pairedCenterQuadraticTerm_valid D (N+1)) h

/-- The constructed constant coefficient is the actual division value at zero. -/
theorem pairedRegularDivisionValue_center_constant (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (he : z.val.Equiv zero) :
    (pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz)).Equiv pairedCenterConstantSum := by
  have hz0 := Small.congr (ofQComplex_valid _) z.property (equiv_symm he)
    (Small.zero (show (0:Rat)≤0 by decide +kernel))
  have h := pairedRegularDivisionValue_quadratic_center_bound z hz 0 (by decide +kernel) hz0
  simp only [Rat.mul_zero] at h
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
  let Q := pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz)
  have vQ := pairedRegularDivisionValue_valid z (LocalODE.interior_bound _ z hz)
  have heq : (sub (sub Q pairedCenterConstantSum) (mul (mul z.val z.val) pairedCenterQuadraticSum)).Equiv
      (sub Q pairedCenterConstantSum) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid vQ pairedCenterConstantSum_valid)
        (mul_valid (mul_valid z.property z.property) pairedCenterQuadraticSum_valid))
      (hright := sub_valid vQ pairedCenterConstantSum_valid)
    let A := ComplexRawQuotient.ofRaw Q vQ
    let C := ComplexRawQuotient.ofRaw pairedCenterConstantSum pairedCenterConstantSum_valid
    let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change Z=0 at hZ
    change (A-C)-(Z*Z)*B=A-C
    rw [hZ]
    grind only
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  exact Small.congr
    (sub_valid (sub_valid vQ pairedCenterConstantSum_valid)
      (mul_valid (mul_valid z.property z.property) pairedCenterQuadraticSum_valid))
    (sub_valid vQ pairedCenterConstantSum_valid) heq h

/-- The constant coefficient agrees with the previously constructed inverse-square value. -/
theorem pairedCenterConstantSum_eq_zeroSquareSum : pairedCenterConstantSum.Equiv pairedZeroSquareSum := by
  have hc := pairedRegularDivisionValue_center_constant pairedZeroScalar pairedZeroScalar_interior
    (equiv_refl _ pairedZeroScalar.property)
  have hz := pairedRegularDivisionValue_at_zero pairedZeroScalar pairedZeroScalar_interior
    (equiv_refl _ pairedZeroScalar.property)
  exact equiv_trans pairedCenterConstantSum_valid
    (pairedRegularDivisionValue_valid pairedZeroScalar (LocalODE.interior_bound _ _ pairedZeroScalar_interior))
    pairedZeroSquareSum_valid (equiv_symm hc) hz

end ComputableAnalysis.ModularForms
