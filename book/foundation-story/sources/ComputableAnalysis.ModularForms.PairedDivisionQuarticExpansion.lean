import ComputableAnalysis.ModularForms.PairedDivisionQuarticPrefixes

/-! Passing the actual quartic center expansion through the convergent division series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private def scalarDifference (x y : Scalar) : Scalar :=
  ⟨sub x.val y.val,sub_valid x.property y.property⟩

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

private theorem quartic_prefix_residual (t c b d : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hc : ∀ n, (c n).Valid)
    (hb : ∀ n, (b n).Valid) (hd : ∀ n, (d n).Valid)
    (Z2 Z4 : Scalar) (N : Nat) :
    (ScalarSeries.block (fun n => sub (sub (sub (t n) (c n)) (mul Z2.val (b n)))
      (mul Z4.val (d n))) 0 N).Equiv
      (sub (sub (sub (ScalarSeries.block t 0 N) (ScalarSeries.block c 0 N))
        (mul Z2.val (ScalarSeries.block b 0 N))) (mul Z4.val (ScalarSeries.block d 0 N))) := by
  let u := fun n => sub (sub (t n) (c n)) (mul Z2.val (b n))
  have hu n : (u n).Valid := sub_valid (sub_valid (ht n) (hc n)) (mul_valid Z2.property (hb n))
  have h1 := representedBlock_sub u (fun n => mul Z4.val (d n)) hu
    (fun n => mul_valid Z4.property (hd n)) 0 N
  have h2 := FunctionTheory.sub_congr (prefix_residual t c b ht hc hb Z2 N)
    (representedPrefix_mul_left d hd Z4 N)
  exact equiv_trans (ScalarSeries.block_valid _
      (fun n => sub_valid (hu n) (mul_valid Z4.property (hd n))) 0 N)
    (sub_valid (ScalarSeries.block_valid u hu 0 N)
      (ScalarSeries.block_valid _ (fun n => mul_valid Z4.property (hd n)) 0 N))
    (sub_valid (sub_valid (sub_valid (ScalarSeries.block_valid t ht 0 N) (ScalarSeries.block_valid c hc 0 N))
      (mul_valid Z2.property (ScalarSeries.block_valid b hb 0 N)))
      (mul_valid Z4.property (ScalarSeries.block_valid d hd 0 N))) h1 h2

/-- The constructed quartic polynomial approximates the actual division value
with a certified sextic remainder at every represented input in the disk. -/
theorem pairedRegularDivisionValue_quartic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (sub (sub (pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz)) pairedCenterConstantSum)
      (mul (mul z.val z.val) pairedCenterQuadraticSum))
      (mul (mul (mul z.val z.val) (mul z.val z.val)) pairedCenterQuarticSum))
      (8192*R*R*R*R*R*R) := by
  let hzz := LocalODE.interior_bound _ z hz
  let Q : Scalar := ⟨pairedRegularDivisionValue z hzz,pairedRegularDivisionValue_valid z hzz⟩
  let A : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let B : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let D : Scalar := ⟨pairedCenterQuarticSum,pairedCenterQuarticSum_valid⟩
  let Z2 := scalarProduct z z
  let Z4 := scalarProduct Z2 Z2
  let t := fun n => (pairedRegularDivisionTerm z hzz n).val
  have ht n : (t n).Valid := (pairedRegularDivisionTerm z hzz n).property
  let q := fun N => (⟨ScalarSeries.block t 0 (N+1),ScalarSeries.block_valid t ht 0 (N+1)⟩ : Scalar)
  let a := fun N => (⟨ScalarSeries.block pairedCenterConstantTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterConstantTerm_valid 0 (N+1)⟩ : Scalar)
  let b := fun N => (⟨ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1)⟩ : Scalar)
  let d := fun N => (⟨ScalarSeries.block pairedCenterQuarticTerm 0 (N+1),
    ScalarSeries.block_valid _ pairedCenterQuarticTerm_valid 0 (N+1)⟩ : Scalar)
  let F := scalarDifference (scalarDifference Q A) (scalarProduct Z2 B)
  let f := fun N => scalarDifference (scalarDifference (q N) (a N)) (scalarProduct Z2 (b N))
  let target := scalarDifference F (scalarProduct Z4 D)
  let p := fun N => (scalarDifference (f N) (scalarProduct Z4 (d N))).val
  have vp N : (p N).Valid := (scalarDifference (f N) (scalarProduct Z4 (d N))).property
  let M2 := DomainFunctions.scalarBound Z2
  let M4 := DomainFunctions.scalarBound Z4
  have hM2 : 0≤M2 := Rat.le_of_lt (DomainFunctions.scalarBound_pos Z2)
  have hM4 : 0≤M4 := Rat.le_of_lt (DomainFunctions.scalarBound_pos Z4)
  let eQ := fun N : Nat => 8*((N+1:Nat):Rat)⁻¹
  let eA := fun N : Nat => 2*((N+1:Nat):Rat)⁻¹
  let eB := fun N : Nat => 4*((N+1:Nat):Rat)⁻¹
  let eD := fun N : Nat => 8*((N+1:Nat):Rat)⁻¹
  let eF := fun N => (eQ N+eA N)+2*M2*eB N
  have heF : ShrinksToZero eF := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 8) (pairedReciprocalTail_shrinks 2))
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 4) (2*M2) (Rat.mul_nonneg (by decide +kernel) hM2))
  have he := RepresentedCauchySum.sum_shrinks _ _ heF
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 8) (2*M4) (Rat.mul_nonneg (by decide +kernel) hM4))
  have hnonneg (N : Nat) (k : Rat) (hk : 0≤k) : 0≤k*((N+1:Nat):Rat)⁻¹ := by
    have hn : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
    exact Rat.mul_nonneg hk (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  apply SeriesLimitLaws.small_of_prefix_bound target.val target.property p vp
    (8192*R*R*R*R*R*R) (fun N => eF N+2*M4*eD N) he
  · intro N
    have h1 := represented_prefix_sub_close Q A (q N) (a N) _ _
      (pairedRegularDivisionValue_close z hzz N) (pairedCenterConstantSum_close N)
    have h2 := representedFactor_difference_small Z2.val B.val (b N).val Z2.property B.property
      (b N).property M2 (eB N) hM2 (hnonneg N 4 (by decide +kernel))
      (DomainFunctions.scalar_small Z2) (pairedCenterQuadraticSum_close N)
    have hf := represented_prefix_sub_close (scalarDifference Q A) (scalarProduct Z2 B)
      (scalarDifference (q N) (a N)) (scalarProduct Z2 (b N)) _ _ h1 h2
    have h3 := representedFactor_difference_small Z4.val D.val (d N).val Z4.property D.property
      (d N).property M4 (eD N) hM4 (hnonneg N 8 (by decide +kernel))
      (DomainFunctions.scalar_small Z4) (pairedCenterQuarticSum_close N)
    exact represented_prefix_sub_close F (scalarProduct Z4 D) (f N) (scalarProduct Z4 (d N)) _ _ hf h3
  · intro N
    have h := pairedRegularDivisionPrefix_quartic_center_bound z hz (N+1) R hR hs
    exact Small.congr
      (ScalarSeries.block_valid _ (fun n => sub_valid
        (sub_valid (sub_valid (ht n) (pairedCenterConstantTerm_valid n))
          (mul_valid Z2.property (pairedCenterQuadraticTerm_valid n)))
        (mul_valid Z4.property (pairedCenterQuarticTerm_valid n))) 0 (N+1)) (vp N)
      (quartic_prefix_residual t pairedCenterConstantTerm pairedCenterQuadraticTerm pairedCenterQuarticTerm ht
        pairedCenterConstantTerm_valid pairedCenterQuadraticTerm_valid pairedCenterQuarticTerm_valid Z2 Z4 (N+1)) h

end ComputableAnalysis.ModularForms
