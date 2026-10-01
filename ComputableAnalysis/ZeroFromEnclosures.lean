import ComputableAnalysis.ZeroIsolation

/-! An exact zero equation derived from shrinking rational range bounds.
The executable root is a supplied sequence of nested input boxes. No zero
identity, root existence, or zero count is stored as a certificate field.
Concrete zeta enclosures and ordinal completeness remain separate obligations. -/
namespace ComputableAnalysis.FunctionTheory.ZeroFromEnclosures

private theorem zero_bounds
    (lo hi rlo rhi : Nat → Rat)
    (hordered : ∀ n, lo n ≤ hi n)
    (hnested : ∀ n m, n ≤ m → lo n ≤ lo m ∧ hi m ≤ hi n)
    (hcover : ∀ k, ∃ m, rlo k ≤ lo m ∧ hi m ≤ rhi k)
    (hzero : ∀ k, rlo k ≤ 0 ∧ 0 ≤ rhi k)
    (hshrink : ∀ eps : QPos, ∃ N, ∀ k, N ≤ k → rhi k - rlo k ≤ eps.val) :
    ∀ n, lo n ≤ 0 ∧ 0 ≤ hi n := by
  intro n
  constructor
  · by_cases h : lo n ≤ 0
    · exact h
    have hp : 0 < lo n := by grind only
    let eps : QPos := ⟨lo n / 2, by simpa only [Rat.div_def] using Rat.mul_pos hp (by decide +kernel : (0 : Rat) < (2 : Rat)⁻¹)⟩
    obtain ⟨N, hN⟩ := hshrink eps
    obtain ⟨m, hm⟩ := hcover N
    have ha := hnested n (max n m) (Nat.le_max_left _ _)
    have hb := hnested m (max n m) (Nat.le_max_right _ _)
    have ho := hordered (max n m)
    have hz := hzero N
    have hs := hN N (Nat.le_refl N)
    dsimp [eps] at hs
    grind only
  · by_cases h : 0 ≤ hi n
    · exact h
    have hp : 0 < -hi n := by grind only
    let eps : QPos := ⟨-hi n / 2, by simpa only [Rat.div_def] using Rat.mul_pos hp (by decide +kernel : (0 : Rat) < (2 : Rat)⁻¹)⟩
    obtain ⟨N, hN⟩ := hshrink eps
    obtain ⟨m, hm⟩ := hcover N
    have ha := hnested n (max n m) (Nat.le_max_left _ _)
    have hb := hnested m (max n m) (Nat.le_max_right _ _)
    have ho := hordered (max n m)
    have hz := hzero N
    have hs := hN N (Nat.le_refl N)
    dsimp [eps] at hs
    grind only

/-- Shrinking sound enclosures that contain zero force an exact zero value.
Containment refers to the computation itself, not to sampled residuals. -/
theorem equiv_zero_of_ranges (y : ComplexRaw) (hy : y.Valid)
    (ranges : Nat → QBox)
    (hcover : ∀ k, ∃ m, (y.compute m).NestedIn (ranges k))
    (hzero : ∀ k, (ranges k).lo ≤ QComplex.zero ∧ QComplex.zero ≤ (ranges k).hi)
    (hshrink : ComplexRaw.WidthsShrinkToZero ranges) : y.Equiv ComplexRaw.zero := by
  have hre := zero_bounds (fun n => (y.compute n).lo.re)
    (fun n => (y.compute n).hi.re) (fun n => (ranges n).lo.re)
    (fun n => (ranges n).hi.re)
    (fun n => (ComplexRaw.valid_ordered hy n).1)
    (fun n m h => ⟨(hy.2.1 n m h).1, (hy.2.1 n m h).2.1⟩)
    (by intro k; obtain ⟨m, hm⟩ := hcover k; exact ⟨m, hm.1.1, hm.2.1⟩)
    (fun k => ⟨(hzero k).1.1, (hzero k).2.1⟩)
    (by intro eps; obtain ⟨N, hN⟩ := hshrink eps; exact ⟨N, fun k hk => (hN k hk).1⟩)
  have him := zero_bounds (fun n => (y.compute n).lo.im)
    (fun n => (y.compute n).hi.im) (fun n => (ranges n).lo.im)
    (fun n => (ranges n).hi.im)
    (fun n => (ComplexRaw.valid_ordered hy n).2)
    (fun n m h => ⟨(hy.2.1 n m h).2.2.1, (hy.2.1 n m h).2.2.2⟩)
    (by intro k; obtain ⟨m, hm⟩ := hcover k; exact ⟨m, hm.1.2, hm.2.2⟩)
    (fun k => ⟨(hzero k).1.2, (hzero k).2.2⟩)
    (by intro eps; obtain ⟨N, hN⟩ := hshrink eps; exact ⟨N, fun k hk => (hN k hk).2⟩)
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  change QBox.Overlaps (y.compute n) (QBox.point QComplex.zero)
  simp only [QBox.Overlaps, QBox.point, QComplex.zero, QComplex.le_def]
  exact ⟨⟨(hre n).1, (him n).1⟩, ⟨(hre n).2, (him n).2⟩⟩

/-- The runtime root reads only the supplied input-box computation. -/
def root (boxes : Nat → QBox) : ComplexRaw where
  compute := boxes

/-- Construct the represented root and derive its exact zero equation from
whole-box range soundness. Validity of the input boxes gives an actual point;
shrinking output ranges give the equation. No count or simplicity is claimed. -/
theorem root_is_zero (f : Map) (boxes ranges : Nat → QBox)
    (hboxes : ComplexRaw.ValidCompute boxes)
    (hdomain : ∀ w : ComplexRaw, w.Valid → (w.compute 0).NestedIn (boxes 0) → f.domain w)
    (hsound : ∀ k w, w.Valid → f.domain w →
      (w.compute k).NestedIn (boxes k) →
      ∃ m, ((f.eval w).compute m).NestedIn (ranges k))
    (hzero : ∀ k, (ranges k).lo ≤ QComplex.zero ∧ QComplex.zero ≤ (ranges k).hi)
    (hshrink : ComplexRaw.WidthsShrinkToZero ranges) :
    (root boxes).Valid ∧ f.domain (root boxes) ∧
      (f.eval (root boxes)).Equiv ComplexRaw.zero := by
  have hv : (root boxes).Valid := hboxes
  have hd : f.domain (root boxes) := hdomain _ hv ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  refine ⟨hv, hd, equiv_zero_of_ranges _ (f.valid _ hv hd) ranges ?_ hzero hshrink⟩
  intro k
  exact hsound k _ hv hd ⟨QComplex.le_refl _, QComplex.le_refl _⟩

/-- The enclosure construction feeds the exact reflection law without an
assumed root equation. Symmetry and uniqueness remain mathematical evidence
for the supplied function, and must be proved for any concrete application. -/
theorem root_on_line (f : Map) (boxes ranges : Nat → QBox)
    (hboxes : ComplexRaw.ValidCompute boxes)
    (hdomain : ∀ w : ComplexRaw, w.Valid → (w.compute 0).NestedIn (boxes 0) → f.domain w)
    (hsound : ∀ k w, w.Valid → f.domain w →
      (w.compute k).NestedIn (boxes k) →
      ∃ m, ((f.eval w).compute m).NestedIn (ranges k))
    (hzero : ∀ k, (ranges k).lo ≤ QComplex.zero ∧ QComplex.zero ≤ (ranges k).hi)
    (hshrink : ComplexRaw.WidthsShrinkToZero ranges)
    (R : ComplexRaw → Prop) (hR : R (root boxes))
    (hDr : f.domain (ZeroIsolation.reflection (root boxes)))
    (hRr : R (ZeroIsolation.reflection (root boxes)))
    (hsym : (f.eval (ZeroIsolation.reflection (root boxes))).Equiv
      (ComplexRaw.conj (f.eval (root boxes))))
    (hunique : ∀ w, w.Valid → f.domain w → R w →
      (f.eval w).Equiv ComplexRaw.zero → w.Equiv (root boxes)) :
    (root boxes).realPart.Equiv (RealRaw.ofRat (1/2)) := by
  obtain ⟨hv, hd, hz⟩ := root_is_zero f boxes ranges hboxes hdomain hsound hzero hshrink
  exact ZeroIsolation.unique_zero_on_line f R hv hd hR hz hDr hRr hsym hunique

end ComputableAnalysis.FunctionTheory.ZeroFromEnclosures
