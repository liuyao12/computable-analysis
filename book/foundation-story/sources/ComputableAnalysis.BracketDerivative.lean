import ComputableAnalysis.ParametrizedLimits

/-! Derivatives of rational-input functions using covered parametrized limits. -/
namespace ComputableAnalysis


namespace BracketDerivative

/-- Brackets remain inside the rational domain at EVERY stage and have
strictly positive width at EVERY stage. Non-emptiness is required separately. -/
def Admissible (domain : Rat → Prop) (x A : RealRaw) : Prop :=
  x.Valid ∧ A.Valid ∧ A.Equiv x ∧
  ∀ n, (A.compute n).lo < (A.compute n).hi ∧
    ∀ r, (A.compute n).lo ≤ r → r ≤ (A.compute n).hi → domain r

/-- The two rational endpoint evaluations are the only evaluations used. -/
def secant (f : Rat → RealRaw) (a b : Rat) : RealRaw :=
  RealRaw.scaleRat (1/(b-a)) (f b-f a)

def secants (f : Rat → RealRaw) (A : RealRaw) : Nat → RealRaw :=
  fun n => secant f (A.compute n).lo (A.compute n).hi

theorem secant_valid {f : Rat → RealRaw} {a b : Rat}
    (ha : (f a).Valid) (hb : (f b).Valid) : (secant f a b).Valid :=
  RealRaw.scaleRat_valid (RealRaw.sub_valid hb ha)

theorem secants_valid {domain : Rat → Prop} {f : Rat → RealRaw} {x A : RealRaw}
    (hf : ∀ r, domain r → (f r).Valid) (hA : Admissible domain x A) :
    ∀ n, (secants f A n).Valid := by
  intro n
  have h := hA.2.2.2 n
  exact secant_valid (hf _ (h.2 _ (Rat.le_refl) (Rat.le_of_lt h.1)))
    (hf _ (h.2 _ (Rat.le_of_lt h.1) (Rat.le_refl)))

/-- A derivative is a common limit of all admissible secants, with no
irrational evaluation of the primary function and no prescribed algorithm. -/
def HasDerivativeAt (domain : Rat → Prop) (f : Rat → RealRaw) (x d : RealRaw) : Prop :=
  x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
  (∃ A, Admissible domain x A) ∧
  ∀ A, Admissible domain x A → RawLimit.HasParametrizedLimit (secants f A) d

/-- Exact compatibility with the previously checked secant-limit interface.
The existential diagonal covers every remaining secant, so no subsequence is
silently substituted for a limit. -/
theorem hasDerivative_iff_secantLimits {domain : Rat → Prop} {f : Rat → RealRaw}
    {x d : RealRaw} : HasDerivativeAt domain f x d ↔
    x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
      (∃ A, Admissible domain x A) ∧
      ∀ A, Admissible domain x A → RawLimit.TendsTo (secants f A) d := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
      fun A hA => RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)⟩
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
      fun A hA => RawLimit.parametrizedLimit_iff.mpr (h.2.2.2.2 A hA)⟩

theorem admissible_congr {domain : Rat → Prop} {x y A : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Admissible domain x A ↔ Admissible domain y A := by
  constructor
  · intro h
    exact ⟨hy,h.2.1,RealRaw.equiv_trans h.2.1 hx hy h.2.2.1 hxy,h.2.2.2⟩
  · intro h
    exact ⟨hx,h.2.1,RealRaw.equiv_trans h.2.1 hy hx h.2.2.1
      (RealRaw.equiv_symm hxy),h.2.2.2⟩

theorem unique {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (hd : HasDerivativeAt domain f x d) (he : HasDerivativeAt domain f x e) : d.Equiv e := by
  obtain ⟨A,hA⟩ := hd.2.2.2.1
  exact RawLimit.HasParametrizedLimit.unique (hd.2.2.2.2 A hA) (he.2.2.2.2 A hA)

theorem congr_point {domain : Rat → Prop} {f : Rat → RealRaw} {x y d : RealRaw}
    (h : HasDerivativeAt domain f x d) (hy : y.Valid) (hxy : x.Equiv y) :
    HasDerivativeAt domain f y d := by
  refine ⟨hy,h.2.1,h.2.2.1,?_,?_⟩
  · obtain ⟨A,hA⟩ := h.2.2.2.1
    exact ⟨A,(admissible_congr h.1 hy hxy).1 hA⟩
  · intro A hA
    exact h.2.2.2.2 A ((admissible_congr h.1 hy hxy).2 hA)

theorem congr_value {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (h : HasDerivativeAt domain f x d) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt domain f x e := by
  exact ⟨h.1,he,h.2.2.1,h.2.2.2.1,fun A hA =>
    RawLimit.parametrizedLimit_iff.mpr
      (RawLimit.congr_target (RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)) he hde)⟩

theorem congr_point_iff {domain : Rat → Prop} {f : Rat → RealRaw} {x y d : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    HasDerivativeAt domain f x d ↔ HasDerivativeAt domain f y d :=
  ⟨fun h => congr_point h hy hxy,
   fun h => congr_point h hx (RealRaw.equiv_symm hxy)⟩

theorem congr_value_iff {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (hd : d.Valid) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt domain f x d ↔ HasDerivativeAt domain f x e :=
  ⟨fun h => congr_value h he hde,
   fun h => congr_value h hd (RealRaw.equiv_symm hde)⟩

theorem congr_function {domain : Rat → Prop} {f g : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d)
    (hg : ∀ r, domain r → (g r).Valid)
    (hfg : ∀ r, domain r → (f r).Equiv (g r)) :
    HasDerivativeAt domain g x d := by
  refine ⟨h.1,h.2.1,hg,h.2.2.2.1,?_⟩
  intro A hA
  apply RawLimit.parametrizedLimit_iff.mpr
  apply RawLimit.congr_sequence (RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)) (secants_valid hg hA)
  intro n
  have ha := hA.2.2.2 n
  have hlo := ha.2 _ (Rat.le_refl) (Rat.le_of_lt ha.1)
  have hhi := ha.2 _ (Rat.le_of_lt ha.1) (Rat.le_refl)
  exact RealRaw.scaleRat_equiv
    (RealRaw.sub_equiv (h.2.2.1 _ hhi) (hg _ hhi)
      (h.2.2.1 _ hlo) (hg _ hlo) (hfg _ hhi) (hfg _ hlo))

end BracketDerivative
end ComputableAnalysis
