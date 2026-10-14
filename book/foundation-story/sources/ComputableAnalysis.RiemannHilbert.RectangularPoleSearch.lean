import ComputableAnalysis.RiemannHilbert.AnnularPoleGeometry
import ComputableAnalysis.RiemannHilbert.PrecisionSearch

/-! Executable clearance from a fixed rectangle boundary. The domain is the
full represented interior or the complement of the closed rectangle. Search
uses rational box comparisons and erased termination evidence. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularPoleSearch
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

def InsideBox (J : QInterval × QInterval) (B : QBox) : Prop :=
  J.1.lo<B.lo.re ∧ B.hi.re<J.1.hi ∧ J.2.lo<B.lo.im ∧ B.hi.im<J.2.hi

def OutsideBox (J : QInterval × QInterval) (B : QBox) : Prop :=
  B.hi.re<J.1.lo ∨ J.1.hi<B.lo.re ∨ B.hi.im<J.2.lo ∨ J.2.hi<B.lo.im

instance (J : QInterval × QInterval) (B : QBox) : Decidable (InsideBox J B) :=
  inferInstanceAs (Decidable (J.1.lo<B.lo.re ∧ B.hi.re<J.1.hi ∧ J.2.lo<B.lo.im ∧ B.hi.im<J.2.hi))

instance (J : QInterval × QInterval) (B : QBox) : Decidable (OutsideBox J B) :=
  inferInstanceAs (Decidable (B.hi.re<J.1.lo ∨ J.1.hi<B.lo.re ∨ B.hi.im<J.2.lo ∨ J.2.hi<B.lo.im))

def domain (inside : Bool) (J : QInterval × QInterval) (z : Scalar) : Prop :=
  if inside then RectanglePoleInterior J z else ¬representedRectangleContains J z

def good (inside : Bool) (J : QInterval × QInterval) (z : Scalar) (n : Nat) : Bool :=
  if inside then decide (InsideBox J (z.val.compute n)) else decide (OutsideBox J (z.val.compute n))

theorem eventually_inside (J : QInterval × QInterval) (z : Scalar) (hz : RectanglePoleInterior J z) :
    ∃ N, ∀ n, N≤n → InsideBox J (z.val.compute n) := by
  obtain ⟨D,hD⟩ := hz
  let E : QPos := ⟨D.val/2,by rw [Rat.div_def]; exact Rat.mul_pos D.property (by decide +kernel)⟩
  obtain ⟨N,hN⟩ := z.property.2.2 E
  refine ⟨N,?_⟩
  intro n hn
  have hw := hN n hn
  have hxl := hD.1 n n
  have hxr := hD.2.1 n n
  have hyl := hD.2.2.1 n n
  have hyr := hD.2.2.2 n n
  change J.1.lo+D.val≤(z.val.compute n).hi.re at hxl
  change (z.val.compute n).lo.re≤J.1.hi-D.val at hxr
  change J.2.lo+D.val≤(z.val.compute n).hi.im at hyl
  change (z.val.compute n).lo.im≤J.2.hi-D.val at hyr
  dsimp [QBox.width,QBox.height,E] at hw
  have hp := D.property
  unfold InsideBox
  grind only

theorem eventually_outside (J : QInterval × QInterval) (z : Scalar)
    (hz : ¬representedRectangleContains J z) : ∃ N, ∀ n, N≤n → OutsideBox J (z.val.compute n) := by
  classical
  have upper (x : RealRaw) (hx : x.Valid) (c : Rat) (h : ¬(RealRaw.ofRat c).Le x) :
      ∃ N, ∀ n, N≤n → (x.compute n).hi<c := by
    obtain ⟨D,hD⟩ := AnnularPoleGeometry.strict_upper x hx c h
    let E : QPos := ⟨D.val/2,by rw [Rat.div_def]; exact Rat.mul_pos D.property (by decide +kernel)⟩
    obtain ⟨N,hN⟩ := hx.2.2 E
    refine ⟨N,?_⟩
    intro n hn
    have hw := hN n hn
    have hb := hD n n
    change (x.compute n).lo≤c-D.val at hb
    dsimp [QInterval.width,E] at hw
    have hp := D.property
    grind only
  have lower (x : RealRaw) (hx : x.Valid) (c : Rat) (h : ¬x.Le (RealRaw.ofRat c)) :
      ∃ N, ∀ n, N≤n → c<(x.compute n).lo := by
    obtain ⟨D,hD⟩ := AnnularPoleGeometry.strict_lower x hx c h
    let E : QPos := ⟨D.val/2,by rw [Rat.div_def]; exact Rat.mul_pos D.property (by decide +kernel)⟩
    obtain ⟨N,hN⟩ := hx.2.2 E
    refine ⟨N,?_⟩
    intro n hn
    have hw := hN n hn
    have hb := hD n n
    change c+D.val≤(x.compute n).hi at hb
    dsimp [QInterval.width,E] at hw
    have hp := D.property
    grind only
  by_cases hxl : (RealRaw.ofRat J.1.lo).Le z.val.realPart
  · by_cases hxr : z.val.realPart.Le (RealRaw.ofRat J.1.hi)
    · by_cases hyl : (RealRaw.ofRat J.2.lo).Le z.val.imagPart
      · have hyr : ¬z.val.imagPart.Le (RealRaw.ofRat J.2.hi) := fun h => hz ⟨hxl,hxr,hyl,h⟩
        obtain ⟨N,hN⟩ := lower _ (imagPart_valid z.property) _ hyr
        exact ⟨N,fun n hn => Or.inr (Or.inr (Or.inr (hN n hn)))⟩
      · obtain ⟨N,hN⟩ := upper _ (imagPart_valid z.property) _ hyl
        exact ⟨N,fun n hn => Or.inr (Or.inr (Or.inl (hN n hn)))⟩
    · obtain ⟨N,hN⟩ := lower _ (realPart_valid z.property) _ hxr
      exact ⟨N,fun n hn => Or.inr (Or.inl (hN n hn))⟩
  · obtain ⟨N,hN⟩ := upper _ (realPart_valid z.property) _ hxl
    exact ⟨N,fun n hn => Or.inl (hN n hn)⟩

theorem eventually_good (inside : Bool) (J : QInterval × QInterval) (z : Scalar) (hz : domain inside J z) :
    ∃ N, ∀ n, N≤n → good inside J z n=true := by
  cases inside
  · obtain ⟨N,hN⟩ := eventually_outside J z hz
    exact ⟨N,fun n hn => by simpa [good] using hN n hn⟩
  · obtain ⟨N,hN⟩ := eventually_inside J z hz
    exact ⟨N,fun n hn => by simpa [good] using hN n hn⟩

def stage (inside : Bool) (J : QInterval × QInterval) (z : Scalar) (hz : domain inside J z) : Nat :=
  PrecisionSearch.firstFrom (good inside J z) (eventually_good inside J z hz) 0

theorem stage_spec (inside : Bool) (J : QInterval × QInterval) (z : Scalar) (hz : domain inside J z) :
    if inside then InsideBox J (z.val.compute (stage inside J z hz))
      else OutsideBox J (z.val.compute (stage inside J z hz)) := by
  have h := (PrecisionSearch.firstFrom_spec (good inside J z) (eventually_good inside J z hz) 0).2
  cases inside <;> simpa [good,stage] using h

def margin (inside : Bool) (J : QInterval × QInterval) (B : QBox) : Rat :=
  if inside then min (B.lo.re-J.1.lo) (min (J.1.hi-B.hi.re) (min (B.lo.im-J.2.lo) (J.2.hi-B.hi.im)))
  else if B.hi.re<J.1.lo then J.1.lo-B.hi.re
  else if J.1.hi<B.lo.re then B.lo.re-J.1.hi
  else if B.hi.im<J.2.lo then J.2.lo-B.hi.im
  else B.lo.im-J.2.hi

theorem margin_positive (inside : Bool) (J : QInterval × QInterval) (B : QBox)
    (h : if inside then InsideBox J B else OutsideBox J B) : 0<margin inside J B := by
  cases inside
  · simp only [Bool.false_eq_true,if_false] at h ⊢
    unfold margin
    simp only [Bool.false_eq_true,if_false]
    split <;> try grind only
    split <;> try grind only
    split <;> grind only [OutsideBox]
  · simp only [if_true] at h ⊢
    unfold margin InsideBox at *
    simp only [if_true]
    grind

def clearance (inside : Bool) (J : QInterval × QInterval) (z : Scalar) (hz : domain inside J z) : QPos :=
  ⟨margin inside J (z.val.compute (stage inside J z hz)),margin_positive inside J _ (stage_spec inside J z hz)⟩

theorem domain_congr (inside : Bool) (J : QInterval × QInterval) (z w : Scalar) (he : z≈w) :
    domain inside J z → domain inside J w := by
  cases inside
  · exact fun hz hw => hz (representedRectangle_congr J w z (equiv_symm he) hw)
  · exact rectanglePoleInterior_congr J z w he

theorem box_bounds (z : Scalar) (n : Nat) : representedRectangleContains
    (⟨(z.val.compute n).lo.re,(z.val.compute n).hi.re⟩,
      ⟨(z.val.compute n).lo.im,(z.val.compute n).hi.im⟩) z :=
  ⟨fun _ m => RealRaw.le_refl z.val.realPart (realPart_valid z.property) n m,
    fun m _ => RealRaw.le_refl z.val.realPart (realPart_valid z.property) m n,
    fun _ m => RealRaw.le_refl z.val.imagPart (imagPart_valid z.property) n m,
    fun m _ => RealRaw.le_refl z.val.imagPart (imagPart_valid z.property) m n⟩

theorem near_box (a : Scalar) (n : Nat) (z : Scalar) (H : Rat) (h : Small (sub z.val a.val) H) :
    representedRectangleContains
      (⟨(a.val.compute n).lo.re-H,(a.val.compute n).hi.re+H⟩,
        ⟨(a.val.compute n).lo.im-H,(a.val.compute n).hi.im+H⟩) z := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro i m
  · have hs := h.1 (max n m) (max n m)
    have ha := valid_nestedIn a.property (show n≤max n m by omega)
    have hz := valid_nestedIn z.property (show m≤max n m by omega)
    change -H≤(z.val.compute (max n m)).hi.re + -(a.val.compute (max n m)).lo.re at hs
    change (a.val.compute n).lo.re-H≤(z.val.compute m).hi.re
    rcases ha with ⟨⟨ha1,ha2⟩,⟨ha3,ha4⟩⟩
    rcases hz with ⟨⟨hz1,hz2⟩,⟨hz3,hz4⟩⟩
    grind only
  · have hs := h.2.1 (max n i) (max n i)
    have ha := valid_nestedIn a.property (show n≤max n i by omega)
    have hz := valid_nestedIn z.property (show i≤max n i by omega)
    change (z.val.compute (max n i)).lo.re + -(a.val.compute (max n i)).hi.re≤H at hs
    change (z.val.compute i).lo.re≤(a.val.compute n).hi.re+H
    rcases ha with ⟨⟨ha1,ha2⟩,⟨ha3,ha4⟩⟩
    rcases hz with ⟨⟨hz1,hz2⟩,⟨hz3,hz4⟩⟩
    grind only
  · have hs := h.2.2.1 (max n m) (max n m)
    have ha := valid_nestedIn a.property (show n≤max n m by omega)
    have hz := valid_nestedIn z.property (show m≤max n m by omega)
    change -H≤(z.val.compute (max n m)).hi.im + -(a.val.compute (max n m)).lo.im at hs
    change (a.val.compute n).lo.im-H≤(z.val.compute m).hi.im
    rcases ha with ⟨⟨ha1,ha2⟩,⟨ha3,ha4⟩⟩
    rcases hz with ⟨⟨hz1,hz2⟩,⟨hz3,hz4⟩⟩
    grind only
  · have hs := h.2.2.2 (max n i) (max n i)
    have ha := valid_nestedIn a.property (show n≤max n i by omega)
    have hz := valid_nestedIn z.property (show i≤max n i by omega)
    change (z.val.compute (max n i)).lo.im + -(a.val.compute (max n i)).hi.im≤H at hs
    change (z.val.compute i).lo.im≤(a.val.compute n).hi.im+H
    rcases ha with ⟨⟨ha1,ha2⟩,⟨ha3,ha4⟩⟩
    rcases hz with ⟨⟨hz1,hz2⟩,⟨hz3,hz4⟩⟩
    grind only

theorem margin_spec (inside : Bool) (J : QInterval × QInterval) (B : QBox) :
    if inside then
      margin inside J B≤B.lo.re-J.1.lo ∧ margin inside J B≤J.1.hi-B.hi.re ∧
        margin inside J B≤B.lo.im-J.2.lo ∧ margin inside J B≤J.2.hi-B.hi.im
    else B.hi.re+margin inside J B≤J.1.lo ∨ J.1.hi+margin inside J B≤B.lo.re ∨
      B.hi.im+margin inside J B≤J.2.lo ∨ J.2.hi+margin inside J B≤B.lo.im := by
  cases inside
  · simp only [Bool.false_eq_true,if_false]
    unfold margin
    simp only [Bool.false_eq_true,if_false]
    split <;> grind only
  · simp only [if_true]
    dsimp [margin]
    grind

def radius (inside : Bool) (J : QInterval × QInterval) (z : Scalar) (hz : domain inside J z) : QPos :=
  ⟨(clearance inside J z hz).val/2,by rw [Rat.div_def]; exact Rat.mul_pos (clearance inside J z hz).property (by decide +kernel)⟩

theorem radius_inside (inside : Bool) (J : QInterval × QInterval) (a : Scalar) (ha : domain inside J a)
    (z : Scalar) (hz : Small (sub z.val a.val) (radius inside J a ha).val) : domain inside J z := by
  let B := a.val.compute (stage inside J a ha)
  let D := clearance inside J a ha
  have hp := D.property
  have hb := near_box a (stage inside J a ha) z (D.val/2) hz
  have hs := margin_spec inside J B
  change (if inside then D.val≤B.lo.re-J.1.lo ∧ D.val≤J.1.hi-B.hi.re ∧
    D.val≤B.lo.im-J.2.lo ∧ D.val≤J.2.hi-B.hi.im else
    B.hi.re+D.val≤J.1.lo ∨ J.1.hi+D.val≤B.lo.re ∨
    B.hi.im+D.val≤J.2.lo ∨ J.2.hi+D.val≤B.lo.im) at hs
  cases inside
  · change ¬representedRectangleContains J z
    intro hj
    simp only [Bool.false_eq_true,if_false] at hs
    rcases hs with hs|hs|hs|hs
    · have h := (RealRaw.le_trans (realPart_valid z.property) hj.1 hb.2.1) 0 0
      change J.1.lo≤B.hi.re+D.val/2 at h
      grind only
    · have h := (RealRaw.le_trans (realPart_valid z.property) hb.1 hj.2.1) 0 0
      change B.lo.re-D.val/2≤J.1.hi at h
      grind only
    · have h := (RealRaw.le_trans (imagPart_valid z.property) hj.2.2.1 hb.2.2.2) 0 0
      change J.2.lo≤B.hi.im+D.val/2 at h
      grind only
    · have h := (RealRaw.le_trans (imagPart_valid z.property) hb.2.2.1 hj.2.2.2) 0 0
      change B.lo.im-D.val/2≤J.2.hi at h
      grind only
  · let E : QPos := ⟨D.val/2,by rw [Rat.div_def]; exact Rat.mul_pos D.property (by decide +kernel)⟩
    refine ⟨E,?_⟩
    simp only [if_true] at hs
    apply representedRectangle_subrectangle _ _ z _ _ _ _ hb <;> dsimp [E] <;> grind only

def openData (inside : Bool) (J : QInterval × QInterval) : ScalarTopology.OpenData (domain inside J) where
  invariant z w he := ⟨domain_congr inside J z w he,domain_congr inside J w z (equiv_symm he)⟩
  radius := radius inside J
  inside := radius_inside inside J

end ComputableAnalysis.RiemannHilbert.RectangularPoleSearch
