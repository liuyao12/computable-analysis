import ComputableAnalysis.BinomialEndpointBounds

/-! Executable selection of a rational exponent chart separated from the
critical exponent. Separation is observable in a finite input interval. -/
namespace ComputableAnalysis.BinomialPower
open Integral ZetaReal

def firstCertified (p : Nat → Prop) [DecidablePred p]
    (hex : ∃ N, ∀ n, N ≤ n → p n) (n : Nat := 0) : Subtype p :=
  if h : p n then ⟨n,h⟩ else firstCertified p hex (n+1)
termination_by Classical.choose hex-n
decreasing_by
  have hs := Classical.choose_spec hex
  have hn : n < Classical.choose hex := by
    by_cases hn : n < Classical.choose hex
    · exact hn
    · exact False.elim (h (hs n (by omega)))
  omega

def AboveOne (s : Real) : Prop := ∃ n, 1 < (s.compute n).lo

private theorem aboveOne_eventual {s : Real} (hs : AboveOne s) :
    ∃ N, ∀ n, N ≤ n → 1 < (s.compute n).lo := by
  obtain ⟨N,hN⟩ := hs
  refine ⟨N,fun n hn => ?_⟩
  have h := (s.valid.2.1 N n hn).1
  change (s.compute N).lo ≤ (s.compute n).lo at h
  grind only

def separationStage (s : Real) (hs : AboveOne s) : Nat :=
  (firstCertified (fun n => 1 < (s.compute n).lo) (aboveOne_eventual hs)).val

theorem separationStage_spec (s : Real) (hs : AboveOne s) :
    1 < (s.compute (separationStage s hs)).lo :=
  (firstCertified (fun n => 1 < (s.compute n).lo) (aboveOne_eventual hs)).property

def separationGap (s : Real) (hs : AboveOne s) : QPos :=
  ⟨(s.compute (separationStage s hs)).lo-1,by have := separationStage_spec s hs; grind⟩

def endpointQ (s : Real) (hs : AboveOne s) : Nat :=
  (firstCertified (fun j => 1/((j : Rat)+1) ≤ (separationGap s hs).val) (by
    have h := shrinksToZero_of_natOverSuccBound (C := 1)
      (width := fun j => 1/((j+1 : Nat) : Rat)) (fun _ => Rat.le_refl) (separationGap s hs)
    simpa only [Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide] using h)).val

def endpointM (s : Real) : Nat := (s.compute 0).hi.num.natAbs+1

theorem endpoint_chart (s : Real) (hs : AboveOne s) {n : Nat}
    (hn : separationStage s hs ≤ n) {t : Rat}
    (ht : (s.compute n).lo ≤ t ∧ t ≤ (s.compute n).hi) : InChart (endpointQ s hs) (endpointM s) t := by
  have hq := (firstCertified (fun j => 1/((j : Rat)+1) ≤ (separationGap s hs).val) (by
    have h := shrinksToZero_of_natOverSuccBound (C := 1)
      (width := fun j => 1/((j+1 : Nat) : Rat)) (fun _ => Rat.le_refl) (separationGap s hs)
    simpa only [Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide] using h)).property
  change 1/((endpointQ s hs : Rat)+1) ≤ (s.compute (separationStage s hs)).lo-1 at hq
  have hlow := (s.valid.2.1 _ _ hn).1
  have hhigh := (s.valid.2.1 0 n (Nat.zero_le n)).2.2
  have hM := rational_upper_natural (s.compute 0).hi
  change (s.compute (separationStage s hs)).lo ≤ (s.compute n).lo at hlow
  change (s.compute n).hi ≤ (s.compute 0).hi at hhigh
  have hupper : (s.compute 0).hi ≤ (endpointM s : Rat) := by
    simpa only [endpointM,Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide] using hM
  constructor <;> grind only

theorem endpointError_shrinks (q m : Nat) : ShrinksToZero (endpointError q m) := by
  have hq := Rat.natCast_nonneg (a := q)
  have hM : 0 ≤ 2*((q : Rat)+1)*bound m :=
    Rat.mul_nonneg (by grind) (bound_nonneg m)
  intro eps
  let e : QPos := ⟨eps.val/2,by have := eps.property; grind⟩
  obtain ⟨N,hN⟩ := geometric_shrinks (ratio_bounds q).1 (ratio_bounds q).2 hM e
  obtain ⟨K,hK⟩ := GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 1) e
  refine ⟨max N K,fun n hn => ?_⟩
  have h1 := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have h2 := hK n (Nat.le_trans (Nat.le_max_right _ _) hn)
  change _ ≤ eps.val/2 at h1 h2
  unfold endpointError
  grind only

theorem endpointCutoff_shrinks (m : Nat) : ShrinksToZero (endpointCutoff m) := by
  intro eps
  obtain ⟨N,hN⟩ := GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 1) eps
  refine ⟨N,fun n hn => ?_⟩
  have hs := hN n hn
  have hp := Rat.mul_nonneg (Rat.natCast_nonneg (a := cutoff m n)) (bound_nonneg m)
  have hden : 0 < 1+(cutoff m n : Rat)*bound m := by grind
  have hi := Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
  have heq : endpointCutoff m n*(1+(cutoff m n : Rat)*bound m)=((1 : Rat)/2)^n := by
    unfold endpointCutoff
    rw [Rat.div_def,Rat.mul_assoc,hi,Rat.mul_one]
  have hmul := Rat.mul_le_mul_of_nonneg_left (show 1 ≤ 1+(cutoff m n : Rat)*bound m by grind)
    (Rat.le_of_lt (endpointCutoff_bounds m n).1)
  rw [heq] at hmul
  grind only

end ComputableAnalysis.BinomialPower
