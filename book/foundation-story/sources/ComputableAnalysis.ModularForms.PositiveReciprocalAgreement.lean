import ComputableAnalysis.PositiveReciprocal
import ComputableAnalysis.ModularForms.RealComplexBridge

/-! Actual multiplicative identity for the executable clipped positive reciprocal. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem lowerClip_equiv (x : RealRaw) (hx : x.Valid) (l : Rat)
    (hl : (RealRaw.ofRat l).Le x) : (RealRaw.lowerClip x l).Equiv x := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid x hx n
  have hb := hl 0 n
  change l ≤ (x.compute n).hi at hb
  change maxRat2 (x.compute n).lo l ≤ (x.compute n).hi ∧ (x.compute n).lo ≤ (x.compute n).hi
  unfold maxRat2
  split <;> exact ⟨by assumption,ho⟩

theorem positiveReciprocal_mul_identity (x : RealRaw) (hx : x.Valid) (l : Rat)
    (hpos : 0 < l) (hl : (RealRaw.ofRat l).Le x) :
    (RealRaw.mul x (RealRaw.positiveReciprocal x l)).Equiv RealRaw.one := by
  let y := RealRaw.lowerClip x l
  have hb (n : Nat) : l ≤ (x.compute n).hi := hl 0 n
  have hy : y.Valid := RealRaw.lowerClip_valid x l hx hb
  have hp : 0 < (y.compute 0).lo := by
    change 0 < maxRat2 (x.compute 0).lo l
    unfold maxRat2
    split <;> grind only
  have hiv := RealRaw.positiveInv_valid hy hp
  have hi : (RealRaw.positiveReciprocal x l).Equiv (RealRaw.positiveInv y 0) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp
      (RealRaw.equiv_refl (RealRaw.positiveInv y 0) hiv n)
    simpa [RealRaw.positiveInv,RealRaw.positiveInvCompute,RealRaw.positiveReciprocal,y] using h
  have hv := RealRaw.positiveReciprocal_valid x l hx hpos hb
  have hm := RealRaw.mul_equiv hx hy hv hiv (RealRaw.equiv_symm (lowerClip_equiv x hx l hl)) hi
  have hu := RealRaw.positiveInv_mul_self_equiv_one hy hp
  exact RealRaw.equiv_trans (RealRaw.mul_valid hx hv) (RealRaw.mul_valid hy hiv)
    (RealRaw.ofRat_valid 1) hm hu

theorem positiveReciprocal_threshold_equiv (x : RealRaw) (hx : x.Valid) (a b : Rat)
    (ha : 0<a) (hb : 0<b) (hla : (RealRaw.ofRat a).Le x) (hlb : (RealRaw.ofRat b).Le x) :
    (RealRaw.positiveReciprocal x a).Equiv (RealRaw.positiveReciprocal x b) := by
  have hva := RealRaw.positiveReciprocal_valid x a hx ha (fun n => hla 0 n)
  have hvb := RealRaw.positiveReciprocal_valid x b hx hb (fun n => hlb 0 n)
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have hoa := RealRaw.interval_order_of_valid _ hva n
  have hob := RealRaw.interval_order_of_valid _ hvb n
  rw [RealRaw.positiveReciprocal_compute x a ha n] at hoa ⊢
  rw [RealRaw.positiveReciprocal_compute x b hb n] at hob ⊢
  exact ⟨hob,hoa⟩

theorem positiveReciprocal_embedding_small (x : RealRaw) (hx : x.Valid) (l : Rat)
    (hp : 0<l) (hl : (RealRaw.ofRat l).Le x) :
    Small (ofRealRaw (RealRaw.positiveReciprocal x l)) (1/l) := by
  have hv := RealRaw.positiveReciprocal_valid x l hx hp (fun n => hl 0 n)
  have hu (n : Nat) := RealRaw.positiveReciprocal_compute_hi_le x l hp n
  have hn (n : Nat) : 0 ≤ ((RealRaw.positiveReciprocal x l).compute n).lo := by
    have hb := hl 0 n
    change l ≤ (x.compute n).hi at hb
    have hh : 0 < (x.compute n).hi := by grind only
    rw [RealRaw.positiveReciprocal_compute x l hp n]
    change 0 ≤ 1/(x.compute n).hi
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr hh)
  have hr : 0≤1/l := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr hp)
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have ho := RealRaw.interval_order_of_valid _ hv m
    have hb := hn m
    change -(1/l) ≤ ((RealRaw.positiveReciprocal x l).compute m).hi
    grind only
  · intro n m
    exact Rat.le_trans (RealRaw.interval_order_of_valid _ hv n) (hu n)
  · intro n m; change -(1/l) ≤ 0; grind only
  · intro n m; exact hr

end ComputableAnalysis.ModularForms
