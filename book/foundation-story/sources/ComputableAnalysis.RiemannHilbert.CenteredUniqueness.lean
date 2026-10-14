import ComputableAnalysis.RiemannHilbert.LocalTransport

/-! Translating uniform local uniqueness to neighborhoods of arbitrary
represented centers. No recentered power-series expansion is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.Centered
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def translate (c z : Scalar) : Scalar := ⟨add c.val z.val, add_valid c.property z.property⟩
def offset (c z : Scalar) : Scalar := ⟨sub z.val c.val, sub_valid z.property c.property⟩
def domain (c : Scalar) (R : Rat) (z : Scalar) : Prop := interior R (offset c z)

theorem interior_congr (R : Rat) (z w : Scalar) (hzw : z.val.Equiv w.val) :
    interior R z → interior R w := by
  intro hz
  obtain ⟨r,hr,hrR,hz⟩ := hz
  exact ⟨r,hr,hrR,Small.congr z.property w.property hzw hz⟩

theorem offset_translate (c z : Scalar) : (offset c (translate c z)).val.Equiv z.val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (offset c (translate c z)).property) (hright := z.property)
  change (ComplexRawQuotient.ofRaw c.val c.property+ComplexRawQuotient.ofRaw z.val z.property)-
    ComplexRawQuotient.ofRaw c.val c.property=ComplexRawQuotient.ofRaw z.val z.property
  grind

theorem translate_offset (c z : Scalar) : (translate c (offset c z)).val.Equiv z.val :=
  SeriesLimitLaws.add_difference z.val c.val z.property c.property

theorem translate_difference (c a z : Scalar) :
    (sub (translate c z).val (translate c a).val).Equiv (sub z.val a.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (translate c z).property (translate c a).property)
    (hright := sub_valid z.property a.property)
  change (ComplexRawQuotient.ofRaw c.val c.property+ComplexRawQuotient.ofRaw z.val z.property)-
    (ComplexRawQuotient.ofRaw c.val c.property+ComplexRawQuotient.ofRaw a.val a.property) =
    ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw a.val a.property
  grind

theorem center_mem (c : Scalar) (R : QPos) : domain c R.val c :=
  ⟨0, by decide, R.property, Small.congr (ofQComplex_valid _) (sub_valid c.property c.property)
    (equiv_symm (add_neg_equiv c.val c.property)) (Small.zero (by decide))⟩

theorem translate_mem (c z : Scalar) (R : Rat) (hz : interior R z) : domain c R (translate c z) :=
  interior_congr R z (offset c (translate c z)) (equiv_symm (offset_translate c z)) hz

theorem translate_zero (c : Scalar) :
    (translate c ⟨zero, ofQComplex_valid _⟩).val.Equiv c.val := add_zero_equiv _ c.property

abbrev Field (c : Scalar) (R : Rat) := (z : Scalar) → domain c R z → Fiber n
abbrev OperatorField (c : Scalar) (R : Rat) := (z : Scalar) → domain c R z → ValueMap (Fiber n) (Fiber n)

def remainder {c : Scalar} {R : Rat} (A : OperatorField (n := n) c R) (f : Field (n := n) c R)
    (a z : Scalar) (ha : domain c R a) (hz : domain c R z) : Fiber n :=
  Fiber.sub (Fiber.sub (f z hz) (f a ha))
    (Fiber.scale ⟨sub z.val a.val, sub_valid z.property a.property⟩ ((A a ha).eval (f a ha)))

def liftField {c : Scalar} {R : Rat} (f : Field (n := n) c R) : UniformLocal.Field (n := n) R :=
  fun z hz => f (translate c z) (translate_mem c z R hz)

def liftOperator {c : Scalar} {R : Rat} (A : OperatorField (n := n) c R) : UniformLocal.OperatorField (n := n) R :=
  fun z hz => A (translate c z) (translate_mem c z R hz)

/-- Matching values at an arbitrary represented center imply equality on a
neighborhood, from the supplied uniform derivative errors and bounds. -/
theorem equal (c : Scalar) (R : QPos) (A : OperatorField (n := n) c R.val) (f g : Field (n := n) c R.val)
    (P B C : Rat) (hP : 0 ≤ P) (hsmall : 2*R.val*P ≤ (1 : Rat)/2) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hinitial : f c (center_mem c R) ≈ g c (center_mem c R))
    (hfB : ∀ z hz, CoordinateBound (f z hz) B)
    (hgB : ∀ z hz, CoordinateBound (g z hz) C)
    (hlinear : ∀ z hz, IsLinear (A z hz))
    (hA : ∀ z hz C, 0 ≤ C → ∀ x, CoordinateBound x C → CoordinateBound ((A z hz).eval x) (P*C))
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A f a z ha hz) (eps.val*H.val))
    (hgrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A g a z ha hz) (eps.val*H.val))
    (z : Scalar) (hz : domain c R.val z) : f z hz ≈ g z hz := by
  have hrem (u : Field (n := n) c R.val) (delta : QPos → QPos)
      (hu : ∀ (eps H : QPos) a z ha hz, H.val ≤ (delta eps).val →
        Small (sub z.val a.val) H.val → CoordinateBound (remainder A u a z ha hz) (eps.val*H.val)) :
      ∀ (eps H : QPos) a z ha hz, H.val ≤ (delta eps).val →
        Small (sub z.val a.val) H.val →
        CoordinateBound (UniformLocal.remainder (liftOperator A) (liftField u) a z ha hz) (eps.val*H.val) := by
    intro eps H a z ha hz hH hza
    have hs := hu eps H (translate c a) (translate c z) (translate_mem c a R.val ha)
      (translate_mem c z R.val hz) hH
      (Small.congr (sub_valid z.property a.property) (sub_valid (translate c z).property (translate c a).property)
        (equiv_symm (translate_difference c a z)) hza)
    let x : Scalar := ⟨sub (translate c z).val (translate c a).val, sub_valid (translate c z).property (translate c a).property⟩
    let y : Scalar := ⟨sub z.val a.val, sub_valid z.property a.property⟩
    exact bound_congr
      (Fiber.sub_congr (Setoid.refl _) (Fiber.scale_congr (a := x) (b := y) (translate_difference c a z) (Setoid.refl _))) hs
  have hzero : (liftField f) ⟨zero, ofQComplex_valid _⟩ (interior_zero R.val R.property) ≈
      (liftField g) ⟨zero, ofQComplex_valid _⟩ (interior_zero R.val R.property) :=
    Setoid.trans (hfcongr _ c _ (center_mem c R) (translate_zero c))
      (Setoid.trans hinitial (Setoid.symm (hgcongr _ c _ (center_mem c R) (translate_zero c))))
  have he := UniformLocal.equal R (liftOperator A) (liftField f) (liftField g) P B C hP hsmall hB hC
    (fun z w hz hw hzw => hfcongr _ _ _ _
      (add_equiv (equiv_refl _ c.property) hzw))
    (fun z w hz hw hzw => hgcongr _ _ _ _
      (add_equiv (equiv_refl _ c.property) hzw))
    hzero (fun _ _ => hfB _ _) (fun _ _ => hgB _ _) (fun _ _ => hlinear _ _)
    (fun _ _ C hC x hx => hA _ _ C hC x hx) deltaF deltaG (hrem f deltaF hfrem) (hrem g deltaG hgrem)
    (offset c z) hz
  exact Setoid.trans (Setoid.symm (hfcongr _ z _ hz (translate_offset c z)))
    (Setoid.trans he (hgcongr _ z _ hz (translate_offset c z)))

end ComputableAnalysis.RiemannHilbert.Centered
