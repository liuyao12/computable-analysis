import ComputableAnalysis.ImproperIntegralBounds

/-! Uniform approximation for supplied compact integrals. This proves a law
from actual compact witnesses and quantitative comparisons; it does not assume
that a numerical candidate is already an integral. -/
namespace ComputableAnalysis.Integral

def onInterval (f : Rat → RealRaw) (a b : Rat)
    (hf : ∀ x, a ≤ x ∧ x ≤ b → (f x).Valid) : FunctionOnInterval where
  raw := { definedAt := fun x => a ≤ x ∧ x ≤ b, compute := fun x _ => (f x).compute }
  lower := a
  upper := b
  defined_on := fun _ h => h
  valid_on := hf

theorem Within.symm {I J : RealRaw} {e : Rat} (h : Within I J e) : Within J I e :=
  fun n m => ⟨(h m n).2, (h m n).1⟩

theorem Within.lower {X Y : RealRaw} {e c : Rat} (hX : X.Valid)
    (h : Within X Y e) (hc : ∀ n, c ≤ (X.compute n).hi) (m : Nat) :
    c-e ≤ (Y.compute m).hi := by
  have h1 : (RealRaw.ofRat c).Le X := fun _ n => hc n
  have h2 : X.Le (RealRaw.add Y (RealRaw.ofRat e)) := fun n m => (h n m).1
  have h3 := RealRaw.le_trans hX h1 h2 0 m
  change c ≤ (Y.compute m).hi+e at h3
  grind only

theorem Within.upper {X Y : RealRaw} {e c : Rat} (hX : X.Valid)
    (h : Within X Y e) (hc : ∀ n, (X.compute n).lo ≤ c) (m : Nat) :
    (Y.compute m).lo ≤ c+e := by
  have h1 : (RealRaw.add Y (RealRaw.ofRat (-e))).Le X := by
    intro m n
    have hh := (h n m).2
    change (Y.compute m).lo+(-e) ≤ (X.compute n).hi
    grind only
  have h2 : X.Le (RealRaw.ofRat c) := fun n _ => hc n
  have h3 := RealRaw.le_trans hX h1 h2 m 0
  change (Y.compute m).lo+(-e) ≤ c at h3
  grind only

def Bounds.transfer {f g : Rat → RealRaw} {a b e : Rat}
    {hf : ∀ x, a ≤ x ∧ x ≤ b → (f x).Valid}
    {hg : ∀ x, a ≤ x ∧ x ≤ b → (g x).Valid}
    (B : Bounds (onInterval f a b hf))
    (hfg : ∀ x, a ≤ x ∧ x ≤ b → Within (f x) (g x) e) :
    Bounds (onInterval g a b hg) where
  partition := B.partition
  lower k := B.lower k-e
  upper k := B.upper k+e
  lower_le := by
    intro k hk x hx n
    exact (hfg x ((B.partition.cell k hk).contains_inDomain hx)).lower
      (hf x ((B.partition.cell k hk).contains_inDomain hx))
      (fun j => B.lower_le k hk x hx j) n
  upper_ge := by
    intro k hk x hx n
    exact (hfg x ((B.partition.cell k hk).contains_inDomain hx)).upper
      (hf x ((B.partition.cell k hk).contains_inDomain hx))
      (fun j => B.upper_ge k hk x hx j) n

private theorem sum_shift (P : RationalPartition a b) (v : Nat → Rat) (e : Rat) :
    rectangleSum (fun k => (P.point (k+1)-P.point k)*(v k+e)) P.pieces =
      rectangleSum (fun k => (P.point (k+1)-P.point k)*v k) P.pieces+(b-a)*e := by
  have h (n : Nat) :
      rectangleSum (fun k => (P.point (k+1)-P.point k)*(v k+e)) n =
      rectangleSum (fun k => (P.point (k+1)-P.point k)*v k) n+(P.point n-P.point 0)*e := by
    induction n with
    | zero => simp only [rectangleSum]; grind
    | succ n ih => simp only [rectangleSum, ih]; grind only
  simpa only [P.left_endpoint, P.right_endpoint] using h P.pieces

theorem Bounds.transfer_sums {f g : Rat → RealRaw} {a b e : Rat}
    {hf : ∀ x, a ≤ x ∧ x ≤ b → (f x).Valid}
    {hg : ∀ x, a ≤ x ∧ x ≤ b → (g x).Valid}
    (B : Bounds (onInterval f a b hf))
    (hfg : ∀ x, a ≤ x ∧ x ≤ b → Within (f x) (g x) e) :
    (B.transfer (hg := hg) hfg).lowerSum=B.lowerSum-(b-a)*e ∧
    (B.transfer (hg := hg) hfg).upperSum=B.upperSum+(b-a)*e := by
  constructor
  · have h := sum_shift B.partition B.lower (-e)
    have he : (fun k => (B.partition.point (k+1)-B.partition.point k)*(B.lower k-e)) =
      (fun k => (B.partition.point (k+1)-B.partition.point k)*(B.lower k+(-e))) := by funext k; grind only
    change rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*(B.lower k-e)) B.partition.pieces = _
    rw [he,h]
    change B.lowerSum+(b-a)*(-e)=B.lowerSum-(b-a)*e
    grind only
  · exact sum_shift B.partition B.upper e

/-- A law for an explicitly supplied uniform approximation and a supplied
limit computation. Every approximating integral must already be justified. -/
theorem hasIntegral_of_uniform_approximation
    {f : Rat → RealRaw} {g : Nat → Rat → RealRaw} {a b : Rat}
    {hf : ∀ x, a ≤ x ∧ x ≤ b → (f x).Valid}
    {hg : ∀ n x, a ≤ x ∧ x ≤ b → (g n x).Valid}
    {I : RealRaw} {J : Nat → RealRaw} {e : Nat → Rat}
    (hab : a ≤ b) (hI : I.Valid)
    (hJ : ∀ n, HasIntegral (onInterval (g n) a b (hg n)) (J n))
    (he : ShrinksToZero e)
    (hfg : ∀ n x, a ≤ x ∧ x ≤ b → Within (f x) (g n x) (e n))
    (hIJ : ∀ n, Within I (J n) (e n)) :
    HasIntegral (onInterval f a b hf) I := by
  refine ⟨hI, ?_, ?_⟩
  · intro B stage
    have est (n : Nat) :
        B.lowerSum-(b-a+1)*e n ≤ (I.compute stage).hi ∧
        (I.compute stage).lo ≤ B.upperSum+(b-a+1)*e n := by
      let D := B.transfer (hg := hg n) (hfg n)
      have hs := B.transfer_sums (hg := hg n) (hfg n)
      have hl := (hIJ n).symm.lower (hJ n).valid (fun k => ((hJ n).bounds D k).1) stage
      have hu := (hIJ n).symm.upper (hJ n).valid (fun k => ((hJ n).bounds D k).2) stage
      change D.lowerSum-e n ≤ _ at hl
      change _ ≤ D.upperSum+e n at hu
      change D.lowerSum=_ ∧ D.upperSum=_ at hs
      rw [hs.1] at hl
      rw [hs.2] at hu
      constructor <;> grind only
    have hL : 0 < b-a+1 := by grind
    constructor
    · by_cases hh : B.lowerSum ≤ (I.compute stage).hi
      · exact hh
      exfalso
      let gap := B.lowerSum-(I.compute stage).hi
      have ht : 0 < gap/(2*(b-a+1)) := by
        rw [Rat.div_def]
        exact Rat.mul_pos (by dsimp [gap]; grind) (Rat.inv_pos.mpr (by grind))
      obtain ⟨N,hN⟩ := he ⟨_,ht⟩
      have hn := hN N (Nat.le_refl _)
      have hm := Rat.mul_le_mul_of_nonneg_right hn (show 0 ≤ 2*(b-a+1) by grind)
      have hi := Rat.mul_inv_cancel (2*(b-a+1)) (by grind)
      have hx := (est N).1
      change e N ≤ gap/(2*(b-a+1)) at hn
      change e N*(2*(b-a+1)) ≤ gap/(2*(b-a+1))*(2*(b-a+1)) at hm
      have hc : gap/(2*(b-a+1))*(2*(b-a+1))=gap := by rw [Rat.div_def]; grind only
      rw [hc] at hm
      dsimp [gap] at hm
      grind only
    · by_cases hh : (I.compute stage).lo ≤ B.upperSum
      · exact hh
      exfalso
      let gap := (I.compute stage).lo-B.upperSum
      have ht : 0 < gap/(2*(b-a+1)) := by
        rw [Rat.div_def]
        exact Rat.mul_pos (by dsimp [gap]; grind) (Rat.inv_pos.mpr (by grind))
      obtain ⟨N,hN⟩ := he ⟨_,ht⟩
      have hn := hN N (Nat.le_refl _)
      have hm := Rat.mul_le_mul_of_nonneg_right hn (show 0 ≤ 2*(b-a+1) by grind)
      have hi := Rat.mul_inv_cancel (2*(b-a+1)) (by grind)
      have hx := (est N).2
      change e N*(2*(b-a+1)) ≤ gap/(2*(b-a+1))*(2*(b-a+1)) at hm
      have hc : gap/(2*(b-a+1))*(2*(b-a+1))=gap := by rw [Rat.div_def]; grind only
      rw [hc] at hm
      dsimp [gap] at hm
      grind only
  · intro eps
    have ht : 0 < eps.val/(4*(b-a+1)) := by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))
    obtain ⟨N,hN⟩ := he ⟨_,ht⟩
    have hh : 0 < eps.val/2 := by have := eps.property; grind
    obtain ⟨B,hB⟩ := (hJ N).tight ⟨_,hh⟩
    let D := B.transfer (hg := hf) (fun x hx => (hfg N x hx).symm)
    refine ⟨D, ?_⟩
    have hs := B.transfer_sums (hg := hf) (fun x hx => (hfg N x hx).symm)
    change D.lowerSum=_ ∧ D.upperSum=_ at hs
    rw [hs.1,hs.2]
    have hn := hN N (Nat.le_refl _)
    have hm := Rat.mul_le_mul_of_nonneg_right hn (show 0 ≤ 4*(b-a+1) by grind)
    have hi := Rat.mul_inv_cancel (4*(b-a+1)) (by grind)
    change e N*(4*(b-a+1)) ≤ eps.val/(4*(b-a+1))*(4*(b-a+1)) at hm
    have hc : eps.val/(4*(b-a+1))*(4*(b-a+1))=eps.val := by rw [Rat.div_def]; grind only
    rw [hc] at hm
    change B.upperSum-B.lowerSum ≤ eps.val/2 at hB
    by_cases hsign : 0 ≤ e N
    · grind only
    · have hprod := Rat.mul_nonneg (show 0 ≤ b-a by grind) (show 0 ≤ -(e N) by grind)
      grind only

theorem Within.congr_left {X Y Z : RealRaw} {e : Rat} (hX : X.Valid) (hY : Y.Valid)
    (heq : X.Equiv Y) (h : Within Y Z e) : Within X Z e := by
  intro n m
  have hXY := RealRaw.le_of_equiv hX hY heq
  have hYX := RealRaw.le_of_equiv hY hX (RealRaw.equiv_symm heq)
  have hYZ : Y.Le (RealRaw.add Z (RealRaw.ofRat e)) := fun i j => (h i j).1
  have hZY : (RealRaw.add Z (RealRaw.ofRat (-e))).Le Y := by
    intro j i
    have hh := (h i j).2
    change (Z.compute j).lo+(-e) ≤ (Y.compute i).hi
    grind only
  have hl := RealRaw.le_trans hY hXY hYZ n m
  have hu := RealRaw.le_trans hY hZY hYX m n
  change (X.compute n).lo ≤ (Z.compute m).hi+e at hl
  change (Z.compute m).lo+(-e) ≤ (X.compute n).hi at hu
  exact ⟨hl,by grind only⟩

/-- Restricting the executable domain of an exact rational function to its
integration segment preserves its already proved integral specification. -/
theorem HasIntegral.exactRat_onInterval {f : Rat → Rat} {a b : Rat} {I : RealRaw}
    (hI : HasIntegral (FunctionOnInterval.exactRat f a b) I) :
    HasIntegral (onInterval (fun x => RealRaw.ofRat (f x)) a b (fun x _ => RealRaw.ofRat_valid _)) I := by
  refine ⟨hI.valid, ?_, ?_⟩
  · intro B n
    let D : Bounds (FunctionOnInterval.exactRat f a b) :=
      { partition := B.partition, lower := B.lower, upper := B.upper,
        lower_le := B.lower_le, upper_ge := B.upper_ge }
    exact hI.bounds D n
  · intro eps
    obtain ⟨B,hB⟩ := hI.tight eps
    let D : Bounds (onInterval (fun x => RealRaw.ofRat (f x)) a b (fun x _ => RealRaw.ofRat_valid _)) :=
      { partition := B.partition, lower := B.lower, upper := B.upper,
        lower_le := B.lower_le, upper_ge := B.upper_ge }
    exact ⟨D,hB⟩

end ComputableAnalysis.Integral
