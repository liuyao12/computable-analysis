import ComputableAnalysis.Calculus

/-!
A sufficient rectangle specification for supplied compact integrals. This is
one checked route, not a mandatory definition for other function-specific
constructions. Existence remains separate from the conditional uniqueness law.
Ported from the in-progress IntegralSpecification without its migration aliases.
-/
namespace ComputableAnalysis.Integral

/-- Literal finite rational summation; no limiting operation is involved. -/
def rectangleSum (term : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n+1 => rectangleSum term n + term n

theorem rectangleSum_mono (f g : Nat → Rat) (n : Nat)
    (h : ∀ k, k < n → f k ≤ g k) : rectangleSum f n ≤ rectangleSum g n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    exact rat_add_le_add (ih (fun k hk => h k (by omega))) (h n (by omega))

theorem rectangleSum_telescope (f : Nat → Rat) (n : Nat) :
    rectangleSum (fun k => f (k+1) - f k) n = f n - f 0 := by
  induction n with
  | zero => simp only [rectangleSum]; grind
  | succ n ih => simp only [rectangleSum, ih]; grind

theorem rectangleSum_scale (f : Nat → Rat) (c : Rat) (n : Nat) :
    rectangleSum (fun k => f k * c) n = rectangleSum f n * c := by
  induction n with
  | zero => simp [rectangleSum]
  | succ n ih => simp only [rectangleSum, ih]; grind

/-- Finite rational lower and upper functions on a rational partition.
Bounds concern represented values, not containment of every evaluator box.
Thus changing an evaluator or its precision schedule does not change them. -/
structure Bounds (F : FunctionOnInterval) where
  partition : RationalPartition F.lower F.upper
  lower : Nat → Rat
  upper : Nat → Rat
  lower_le : ∀ k (hk : k < partition.pieces) x
    (hx : (partition.cell k hk).contains x) n,
    lower k ≤ (F.compute x ((partition.cell k hk).contains_inDomain hx) n).hi
  upper_ge : ∀ k (hk : k < partition.pieces) x
    (hx : (partition.cell k hk).contains x) n,
    (F.compute x ((partition.cell k hk).contains_inDomain hx) n).lo ≤ upper k

namespace Bounds

def lowerSum {F : FunctionOnInterval} (B : Bounds F) : Rat :=
  rectangleSum
    (fun k => (B.partition.point (k+1) - B.partition.point k) * B.lower k)
    B.partition.pieces

def upperSum {F : FunctionOnInterval} (B : Bounds F) : Rat :=
  rectangleSum
    (fun k => (B.partition.point (k+1) - B.partition.point k) * B.upper k)
    B.partition.pieces

def Encloses {F : FunctionOnInterval} (B : Bounds F) (I : RealRaw) : Prop :=
  ∀ n, B.lowerSum ≤ (I.compute n).hi ∧ (I.compute n).lo ≤ B.upperSum

end Bounds

/-- Arbitrarily tight finite bounds. This is a proposition about the integrand,
not an integral evaluator, a chosen rate, or an existence axiom. -/
def HasTightBounds (F : FunctionOnInterval) : Prop :=
  ∀ eps : QPos, ∃ B : Bounds F, B.upperSum - B.lowerSum ≤ eps.val

/-- A supplied raw real is the definite integral on the function's rational
interval. Neither existence nor a preferred implementation is built in. -/
structure HasIntegral (F : FunctionOnInterval) (I : RealRaw) : Prop where
  valid : I.Valid
  bounds : ∀ B : Bounds F, B.Encloses I
  tight : HasTightBounds F

/-- Two values obeying the same arbitrarily tight rational bounds coincide.
This is a separation proof using rational arithmetic only. -/
theorem equiv_of_bounds {F : FunctionOnInterval} {I J : RealRaw}
    (htight : HasTightBounds F)
    (hI : ∀ B : Bounds F, B.Encloses I)
    (hJ : ∀ B : Bounds F, B.Encloses J) : I.Equiv J := by
  have hle : ∀ (X Y : RealRaw),
      (∀ B : Bounds F, B.Encloses X) →
      (∀ B : Bounds F, B.Encloses Y) → X.Le Y := by
    intro X Y hX hY n m
    by_cases h : (X.compute n).lo ≤ (Y.compute m).hi
    · exact h
    exfalso
    have hgap : 0 < ((X.compute n).lo - (Y.compute m).hi) / 2 := by grind
    obtain ⟨B, hB⟩ := htight ⟨_, hgap⟩
    have hx := (hX B n).2
    have hy := (hY B m).1
    change B.upperSum - B.lowerSum ≤
      ((X.compute n).lo - (Y.compute m).hi) / 2 at hB
    grind
  exact RealRaw.equiv_of_le_of_ge (hle I J hI hJ) (hle J I hJ hI)

/-- Uniqueness is independent of every existence theorem and every algorithm. -/
theorem HasIntegral.unique {F : FunctionOnInterval} {I J : RealRaw}
    (hI : HasIntegral F I) (hJ : HasIntegral F J) : I.Equiv J :=
  equiv_of_bounds hI.tight hI.bounds hJ.bounds

/-- The specification survives replacement by any equivalent valid raw name. -/
theorem HasIntegral.congr {F : FunctionOnInterval} {I J : RealRaw}
    (hI : HasIntegral F I) (hJ : J.Valid) (heq : I.Equiv J) :
    HasIntegral F J := by
  refine ⟨hJ, ?_, hI.tight⟩
  intro B n
  have hlow : (RealRaw.ofRat B.lowerSum).Le I := fun _ m => (hI.bounds B m).1
  have hupp : I.Le (RealRaw.ofRat B.upperSum) := fun m _ => (hI.bounds B m).2
  exact ⟨RealRaw.le_trans hI.valid hlow (RealRaw.le_of_equiv hI.valid hJ heq) 0 n,
    RealRaw.le_trans hI.valid (RealRaw.le_of_equiv hJ hI.valid
      (RealRaw.equiv_symm heq)) hupp n 0⟩

theorem ExactCellOrderPreservation.encloses {f P : Rat → Rat} {a b : Rat}
    (hP : ExactCellOrderPreservation f (fun u v => P v - P u) a b) :
    ∀ B : Bounds (FunctionOnInterval.exactRat f a b),
      B.Encloses (RealRaw.ofRat (P b-P a)) := by
  intro B n
  have hlo := rectangleSum_mono
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.lower k)
    (fun k => P (B.partition.point (k+1))-P (B.partition.point k))
    B.partition.pieces (by
      intro k hk
      let hcell := B.partition.cell k hk
      exact hP.lower_const hcell.lower_mem hcell.ordered hcell.upper_mem
        (fun {x} hx hy => B.lower_le k hk x ⟨hx, hy⟩ 0))
  have hhi := rectangleSum_mono
    (fun k => P (B.partition.point (k+1))-P (B.partition.point k))
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.upper k)
    B.partition.pieces (by
      intro k hk
      let hcell := B.partition.cell k hk
      exact hP.upper_const hcell.lower_mem hcell.ordered hcell.upper_mem
        (fun {x} hx hy => B.upper_ge k hk x ⟨hx, hy⟩ 0))
  rw [rectangleSum_telescope (fun k => P (B.partition.point k)), B.partition.left_endpoint,
    B.partition.right_endpoint] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem HasIntegral.ftc_exact {f P : Rat → Rat} {a b : Rat} {I : RealRaw}
    (hI : HasIntegral (FunctionOnInterval.exactRat f a b) I)
    (hP : ExactCellOrderPreservation f (fun u v => P v - P u) a b) :
    I.Equiv (RealRaw.ofRat (P b-P a)) :=
  equiv_of_bounds hI.tight hI.bounds hP.encloses

/-- Existence for an exact endpoint algorithm is separate from the FTC law. -/
theorem ExactCellOrderPreservation.hasIntegral {f P : Rat → Rat} {a b : Rat}
    (hP : ExactCellOrderPreservation f (fun u v => P v - P u) a b)
    (htight : HasTightBounds (FunctionOnInterval.exactRat f a b)) :
    HasIntegral (FunctionOnInterval.exactRat f a b) (RealRaw.ofRat (P b-P a)) :=
  ⟨RealRaw.ofRat_valid _, hP.encloses, htight⟩


/-- Executable endpoint rectangles for a supplied decreasing rational function. -/
def antitoneBounds (f : Rat → Rat) (a b : Rat) (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → f y ≤ f x)
    (N : Nat) (hN : 0 < N) : Bounds (FunctionOnInterval.exactRat f a b) where
  partition := RationalPartition.uniform a b N hN hab
  lower k := f (leftPoint a b N (k+1))
  upper k := f (leftPoint a b N k)
  lower_le := by
    intro k hk x hx n
    exact hf x _ (Rat.le_trans (RationalPartition.cell _ k hk).lower_mem hx.1)
      hx.2 (RationalPartition.cell _ k hk).upper_mem
  upper_ge := by
    intro k hk x hx n
    exact hf _ x (RationalPartition.cell _ k hk).lower_mem hx.1
      (Rat.le_trans hx.2 (RationalPartition.cell _ k hk).upper_mem)

theorem antitoneBounds_gap (f : Rat → Rat) (a b : Rat) (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → f y ≤ f x)
    (N : Nat) (hN : 0 < N) :
    (antitoneBounds f a b hab hf N hN).upperSum -
      (antitoneBounds f a b hab hf N hN).lowerSum =
        (b-a)*(f a-f b)/(N : Rat) := by
  have h : ∀ n, rectangleSum (fun k => mesh a b N*f (leftPoint a b N k)) n -
      rectangleSum (fun k => mesh a b N*f (leftPoint a b N (k+1))) n =
      mesh a b N*(f a-f (leftPoint a b N n)) := by
    intro n
    induction n with
    | zero => simp only [rectangleSum, leftPoint_zero]; grind
    | succ n ih => simp only [rectangleSum]; grind only
  unfold Bounds.upperSum Bounds.lowerSum antitoneBounds
  simp only [RationalPartition.uniform, leftPoint_step]
  rw [h, leftPoint_endpoint hN]
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hN)]
  simp only [Rat.div_def]
  grind only

/-- Every decreasing rational function on this particular compact segment has
arbitrarily tight endpoint rectangles. This is a sufficient construction lemma,
not a restriction on other integral specifications. -/
theorem antitone_tight (f : Rat → Rat) (a b : Rat) (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → f y ≤ f x) :
    HasTightBounds (FunctionOnInterval.exactRat f a b) := by
  intro eps
  let C := (b-a)*(f a-f b)
  have hC : 0 ≤ C := Rat.mul_nonneg (by grind) (by have := hf a b (Rat.le_refl) hab (Rat.le_refl); grind)
  have hpos : 0 < C+1 := by grind
  have he : 0 < eps.val/(C+1) := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hpos)
  obtain ⟨N,hN⟩ := shrinksToZero_of_natOverSuccBound (C := 1)
    (width := fun n => 1/((n+1 : Nat) : Rat)) (fun _ => Rat.le_refl) ⟨_,he⟩
  refine ⟨antitoneBounds f a b hab hf (N+1) (by omega), ?_⟩
  rw [antitoneBounds_gap]
  have ht := hN N (Nat.le_refl _)
  have hm := Rat.mul_le_mul_of_nonneg_right ht (Rat.le_of_lt hpos)
  have hc := Rat.mul_inv_cancel (C+1) (Rat.ne_of_gt hpos)
  have hn : 0 ≤ (((N+1 : Nat) : Rat)⁻¹) :=
    Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (by omega)))
  change C / ((N+1 : Nat) : Rat) ≤ eps.val
  simp only [Rat.div_def, Rat.one_mul] at hm ⊢
  have hh : eps.val*(C+1)⁻¹*(C+1)=eps.val := by grind only
  rw [hh] at hm
  grind only

/-- The increasing case uses the same finite rectangles with signs reversed. -/
theorem monotone_tight (f : Rat → Rat) (a b : Rat) (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → f x ≤ f y) :
    HasTightBounds (FunctionOnInterval.exactRat f a b) := by
  intro eps
  obtain ⟨B,hB⟩ := antitone_tight (fun x => -f x) a b hab
    (fun x y hx hxy hy => by have := hf x y hx hxy hy; grind) eps
  let C : Bounds (FunctionOnInterval.exactRat f a b) :=
    { partition := B.partition
      lower := fun k => -B.upper k
      upper := fun k => -B.lower k
      lower_le := by intro k hk x hx n; have h := B.upper_ge k hk x hx n; change -f x ≤ B.upper k at h; change -B.upper k ≤ f x; grind
      upper_ge := by intro k hk x hx n; have h := B.lower_le k hk x hx n; change B.lower k ≤ -f x at h; change f x ≤ -B.lower k; grind }
  have hn (g : Nat → Rat) (n : Nat) : rectangleSum (fun k => -g k) n = -rectangleSum g n := by
    induction n with
    | zero => simp only [rectangleSum]; grind
    | succ n ih => simp only [rectangleSum, ih]; grind only
  have hu : C.upperSum = -B.lowerSum := by
    unfold Bounds.upperSum Bounds.lowerSum C
    rw [show (fun k => (B.partition.point (k+1)-B.partition.point k)* -B.lower k) =
      (fun k => -((B.partition.point (k+1)-B.partition.point k)*B.lower k)) by funext k; grind only, hn]
  have hl : C.lowerSum = -B.upperSum := by
    unfold Bounds.upperSum Bounds.lowerSum C
    rw [show (fun k => (B.partition.point (k+1)-B.partition.point k)* -B.upper k) =
      (fun k => -((B.partition.point (k+1)-B.partition.point k)*B.upper k)) by funext k; grind only, hn]
  refine ⟨C, ?_⟩
  rw [hu,hl]
  grind only

end ComputableAnalysis.Integral
