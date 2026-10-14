import ComputableAnalysis.BracketDerivativeConstruction

/-! Real differentiability by shrinking intervals covering every nearby
rational-input secant. These are precisely real boxes of imaginary height zero.
The older endpoint-bracket limit is retained as a weaker consequence. -/
namespace ComputableAnalysis.RealSecantDerivative
open RawLimit BracketDerivative
set_option maxHeartbeats 2000000

/-- Every distinct ordered pair inside the entire input neighborhood. Ordering
only chooses a canonical orientation; reversing the endpoints preserves the slope. -/
def observations (f : Rat → RealRaw) (A : RealRaw) (n : Nat) (y : RealRaw) : Prop :=
  ∃ a b : Rat, (A.compute n).lo≤a ∧ a<b ∧ b≤(A.compute n).hi ∧ y=secant f a b

theorem observations_antitone {f : Rat → RealRaw} {A : RealRaw} (hA : A.Valid) :
    ∀ i j, i≤j → ∀ y, observations f A j y → observations f A i y := by
  rintro i j hij y ⟨a,b,ha,hab,hb,hy⟩
  have nest := hA.2.1 i j hij
  exact ⟨a,b,Rat.le_trans nest.1 ha,hab,Rat.le_trans hb nest.2.2,hy⟩

theorem observations_inhabited {domain : Rat → Prop} {f : Rat → RealRaw} {x A : RealRaw}
    (hf : ∀ r, domain r → (f r).Valid) (hA : Admissible domain x A) :
    ∀ n, ∃ y, y.Valid ∧ observations f A n y := by
  intro n
  have hm := hA.2.2.2 n
  exact ⟨secant f (A.compute n).lo (A.compute n).hi,
    secant_valid (hf _ (hm.2 _ Rat.le_refl (Rat.le_of_lt hm.1)))
      (hf _ (hm.2 _ (Rat.le_of_lt hm.1) Rat.le_refl)),
    _,_,Rat.le_refl,hm.1,Rat.le_refl,rfl⟩

/-- The public real shrinking-box condition. Rational evaluations stay primary,
input and output refinement remain independent, and every pair is covered.
A supplied nonempty bracket family preserves relative closed-domain endpoints. -/
def HasDerivativeAt (domain : Rat → Prop) (f : Rat → RealRaw) (x d : RealRaw) : Prop :=
  x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
  (∃ A, Admissible domain x A) ∧
  ∀ A, Admissible domain x A → HasEnclosureValue (observations f A) d

theorem hasDerivative_iff_neighborhoods {domain : Rat → Prop} {f : Rat → RealRaw} {x d : RealRaw} :
    HasDerivativeAt domain f x d ↔
    x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
    (∃ A, Admissible domain x A) ∧
    ∀ A, Admissible domain x A → NeighborhoodTendsTo (observations f A) d := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA =>
      (enclosureValue_iff (observations_antitone hA.2.1)).mp (h.2.2.2.2 A hA)⟩
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA =>
      (enclosureValue_iff (observations_antitone hA.2.1)).mpr (h.2.2.2.2 A hA)⟩

/-- Shrinking boxes imply the previous straddling-endpoint derivative law.
The converse is deliberately not asserted for arbitrary real functions. -/
theorem HasDerivativeAt.bracket {domain : Rat → Prop} {f : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d) : BracketDerivative.HasDerivativeAt domain f x d := by
  apply BracketDerivative.hasDerivative_iff_secantLimits.mpr
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA => ⟨h.2.1,secants_valid h.2.2.1 hA,?_⟩⟩
  have hn := (enclosureValue_iff (observations_antitone hA.2.1)).mp (h.2.2.2.2 A hA)
  intro k eps
  obtain ⟨N,hN⟩ := hn.2 k eps
  refine ⟨N,fun n hnn => hN _ (observations_antitone hA.2.1 N n hnn _ ?_)⟩
  exact ⟨_,_,Rat.le_refl,(hA.2.2.2 n).1,Rat.le_refl,rfl⟩

theorem unique {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (h : HasDerivativeAt domain f x d) (k : HasDerivativeAt domain f x e) : d.Equiv e :=
  BracketDerivative.unique h.bracket k.bracket

theorem congr_point {domain : Rat → Prop} {f : Rat → RealRaw} {x y d : RealRaw}
    (h : HasDerivativeAt domain f x d) (hy : y.Valid) (he : x.Equiv y) :
    HasDerivativeAt domain f y d := by
  refine ⟨hy,h.2.1,h.2.2.1,?_,?_⟩
  · obtain ⟨A,hA⟩ := h.2.2.2.1
    exact ⟨A,(admissible_congr h.1 hy he).mp hA⟩
  · intro A hA
    exact h.2.2.2.2 A ((admissible_congr h.1 hy he).mpr hA)

theorem congr_value {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (h : HasDerivativeAt domain f x d) (he : e.Valid) (eq : d.Equiv e) :
    HasDerivativeAt domain f x e :=
  ⟨h.1,he,h.2.2.1,h.2.2.2.1,fun A hA => (h.2.2.2.2 A hA).congr_value he eq⟩

theorem congr_function {domain : Rat → Prop} {f g : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d) (hg : ∀ r, domain r → (g r).Valid)
    (eq : ∀ r, domain r → (f r).Equiv (g r)) : HasDerivativeAt domain g x d := by
  refine ⟨h.1,h.2.1,hg,h.2.2.2.1,fun A hA => ?_⟩
  obtain ⟨hd,Q,n,m,hn,hm,hC,hCd,cover⟩ := h.2.2.2.2 A hA
  refine ⟨hd,Q,n,m,hn,hm,hC,hCd,?_⟩
  rintro k y ⟨a,b,ha,hab,hb,rfl⟩
  have mem := (hA.2.2.2 (n k)).2
  have da := mem a ha (Rat.le_trans (Rat.le_of_lt hab) hb)
  have db := mem b (Rat.le_trans ha (Rat.le_of_lt hab)) hb
  exact inInterval_congr (secant_valid (h.2.2.1 a da) (h.2.2.1 b db))
    (secant_valid (hg a da) (hg b db))
    (RealRaw.scaleRat_equiv (RealRaw.sub_equiv (h.2.2.1 b db) (hg b db)
      (h.2.2.1 a da) (hg a da) (eq b db) (eq a da)))
    (cover k _ ⟨a,b,ha,hab,hb,rfl⟩)

/-- All secants inside a smaller neighborhood lie in the actual outer-secant
box. Convexity supplies order; validity supplies the shrinking limit. -/
theorem outerDerivative_hasDerivative {domain : Rat → Prop} {f : Rat → RealRaw}
    {x : RealRaw} (l u v r : Nat → Rat) (prec : Nat → Nat)
    (hx : x.Valid) (hf : ∀ t, domain t → (f t).Valid)
    (existsBracket : ∃ A, Admissible domain x A)
    (hd : (outerDerivative f l u v r prec).Valid)
    (points : ∀ n, domain (l n) ∧ domain (u n) ∧ domain (v n) ∧ domain (r n))
    (order : ∀ w a b z, domain w → domain a → domain b → domain z →
      w<a → a≤b → b<z → (secant f w a).Le (secant f b z))
    (neighborhood : ∀ n, l n<u n ∧ v n<r n ∧
      ∃ k, u n<(x.compute k).lo ∧ (x.compute k).hi<v n) :
    HasDerivativeAt domain f x (outerDerivative f l u v r prec) := by
  refine ⟨hx,hd,hf,existsBracket,fun A hA => ?_⟩
  apply (enclosureValue_iff (observations_antitone hA.2.1)).mpr
  refine ⟨hd,?_⟩
  intro m eps
  obtain ⟨hlu,hvr,k,huk,hkv⟩ := neighborhood m
  obtain ⟨N,hN⟩ := eventually_inside hA huk hkv
  refine ⟨N,?_⟩
  rintro y ⟨a,b,ha,hab,hb,rfl⟩
  have hi := hN N (Nat.le_refl _)
  have mem := (hA.2.2.2 N).2
  have da := mem a ha (Rat.le_trans (Rat.le_of_lt hab) hb)
  have db := mem b (Rat.le_trans ha (Rat.le_of_lt hab)) hb
  have left := order (l m) (u m) a b (points m).1 (points m).2.1 da db
    hlu (by grind only) hab
  have right := order a b (v m) (r m) da db (points m).2.2.1 (points m).2.2.2
    hab (by grind only) hvr
  constructor
  · intro i j
    have h := left (prec m) j
    change ((outerDerivative f l u v r prec).compute m).lo-eps.val≤((secant f a b).compute j).hi
    dsimp [outerDerivative,QInterval.hull]
    have hp := eps.property
    grind
  · intro i j
    have h := right i (prec m)
    change ((secant f a b).compute i).lo≤((outerDerivative f l u v r prec).compute m).hi+eps.val
    dsimp [outerDerivative,QInterval.hull]
    have hp := eps.property
    grind

/-- Concavity reverses the outer secants, while using the same literal hull
algorithm. No negated surrogate function or minimum pair separation is needed. -/
theorem concave_outerDerivative_hasDerivative {domain : Rat → Prop} {f : Rat → RealRaw}
    {x : RealRaw} (l u v r : Nat → Rat) (prec : Nat → Nat)
    (hx : x.Valid) (hf : ∀ t, domain t → (f t).Valid)
    (existsBracket : ∃ A, Admissible domain x A)
    (hd : (outerDerivative f l u v r prec).Valid)
    (points : ∀ n, domain (l n) ∧ domain (u n) ∧ domain (v n) ∧ domain (r n))
    (order : ∀ w a b z, domain w → domain a → domain b → domain z →
      w<a → a≤b → b<z → (secant f b z).Le (secant f w a))
    (neighborhood : ∀ n, l n<u n ∧ v n<r n ∧
      ∃ k, u n<(x.compute k).lo ∧ (x.compute k).hi<v n) :
    HasDerivativeAt domain f x (outerDerivative f l u v r prec) := by
  refine ⟨hx,hd,hf,existsBracket,fun A hA => ?_⟩
  apply (enclosureValue_iff (observations_antitone hA.2.1)).mpr
  refine ⟨hd,?_⟩
  intro m eps
  obtain ⟨hlu,hvr,k,huk,hkv⟩ := neighborhood m
  obtain ⟨N,hN⟩ := eventually_inside hA huk hkv
  refine ⟨N,?_⟩
  rintro y ⟨a,b,ha,hab,hb,rfl⟩
  have hi := hN N (Nat.le_refl _)
  have mem := (hA.2.2.2 N).2
  have da := mem a ha (Rat.le_trans (Rat.le_of_lt hab) hb)
  have db := mem b (Rat.le_trans ha (Rat.le_of_lt hab)) hb
  have upper := order (l m) (u m) a b (points m).1 (points m).2.1 da db
    hlu (by grind only) hab
  have lower := order a b (v m) (r m) da db (points m).2.2.1 (points m).2.2.2
    hab (by grind only) hvr
  constructor
  · intro i j
    have h := lower (prec m) j
    change ((outerDerivative f l u v r prec).compute m).lo-eps.val≤((secant f a b).compute j).hi
    dsimp [outerDerivative,QInterval.hull]
    have hp := eps.property
    grind
  · intro i j
    have h := upper i (prec m)
    change ((secant f a b).compute i).lo≤((outerDerivative f l u v r prec).compute m).hi+eps.val
    dsimp [outerDerivative,QInterval.hull]
    have hp := eps.property
    grind

/-- A literal zero-height rational rectangle. -/
def flatBox (I : QInterval) : QBox := {lo:={re:=I.lo,im:=0},hi:={re:=I.hi,im:=0}}

theorem flatBox_height (I : QInterval) : (flatBox I).height=0 := by
  simp [flatBox,QBox.height,Rat.sub_self]

theorem flat_compute (x : RealRaw) (n : Nat) :
    (ComplexRaw.ofRealRaw x).compute n=flatBox (x.compute n) := rfl

theorem flat_realPart_compute (x : RealRaw) (n : Nat) :
    (ComplexRaw.ofRealRaw x).realPart.compute n=x.compute n := rfl

theorem flat_imagPart (x : RealRaw) : (ComplexRaw.ofRealRaw x).imagPart=RealRaw.ofRat 0 := rfl

theorem flat_equiv_iff (x y : RealRaw) :
    (ComplexRaw.ofRealRaw x).Equiv (ComplexRaw.ofRealRaw y) ↔ x.Equiv y := by
  constructor
  · intro h n
    have b := (ComplexRaw.compareAt_overlap_iff _ _ n n).mp (h n)
    exact (RealRaw.compareAt_overlap_iff _ _ n n).mpr ⟨b.1.1,b.2.1⟩
  · intro h n
    have b := (RealRaw.compareAt_overlap_iff _ _ n n).mp (h n)
    exact (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
      ⟨⟨b.1,Rat.le_refl⟩,⟨b.2,Rat.le_refl⟩⟩

/-- Exact represented membership in the real rectangle with imaginary height zero. -/
def FlatContains (I : QInterval) (z : ComplexRaw) : Prop :=
  InInterval z.realPart I ∧ InInterval z.imagPart {lo:=0,hi:=0}

def HasFlatEnclosureValue (tests : Nat → RealRaw → Prop) (c : RealRaw) : Prop :=
  ∃ Q : Nat → Nat → QInterval, ∃ n m : Nat → Nat,
    Cofinal n ∧ Cofinal m ∧ (ComplexRaw.ofRealRaw (diagonal Q n m)).Valid ∧
    (ComplexRaw.ofRealRaw (diagonal Q n m)).Equiv (ComplexRaw.ofRealRaw c) ∧
    ∀ k y, tests (n k) y → FlatContains (Q (n k) (m k)) (ComplexRaw.ofRealRaw y)

theorem flat_enclosure_iff {tests : Nat → RealRaw → Prop} {c : RealRaw} (hc : c.Valid) :
    HasFlatEnclosureValue tests c ↔ HasEnclosureValue tests c := by
  constructor
  · rintro ⟨Q,n,m,hn,hm,hv,he,cover⟩
    exact ⟨hc,Q,n,m,hn,hm,ComplexRaw.realPart_valid hv,(flat_equiv_iff _ _).mp he,
      fun k y hy => (cover k y hy).1⟩
  · rintro ⟨_,Q,n,m,hn,hm,hv,he,cover⟩
    refine ⟨Q,n,m,hn,hm,ComplexRaw.ofRealRaw_valid _ hv,(flat_equiv_iff _ _).mpr he,?_⟩
    intro k y hy
    exact ⟨cover k y hy,RealRaw.le_refl _ (RealRaw.ofRat_valid 0),
      RealRaw.le_refl _ (RealRaw.ofRat_valid 0)⟩

/-- The real derivative condition is exactly the zero-height rectangle condition.
No positive imaginary padding or complex open-domain hypothesis is introduced. -/
theorem hasDerivative_iff_flatBoxes {domain : Rat → Prop} {f : Rat → RealRaw} {x d : RealRaw} :
    HasDerivativeAt domain f x d ↔
    x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
    (∃ A, Admissible domain x A) ∧
    ∀ A, Admissible domain x A → HasFlatEnclosureValue (observations f A) d := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA => (flat_enclosure_iff h.2.1).mpr (h.2.2.2.2 A hA)⟩
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA => (flat_enclosure_iff h.2.1).mp (h.2.2.2.2 A hA)⟩

/-- Restriction keeps real endpoint laws when the smaller bracket family is supplied. -/
theorem restrict {domain small : Rat → Prop} {f : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d) (inside : ∀ q, small q → domain q)
    (inhabited : ∃ A, Admissible small x A) : HasDerivativeAt small f x d := by
  refine ⟨h.1,h.2.1,fun r hr => h.2.2.1 r (inside r hr),inhabited,fun A hA => ?_⟩
  exact h.2.2.2.2 A ⟨hA.1,hA.2.1,hA.2.2.1,fun n =>
    ⟨(hA.2.2.2 n).1,fun r hl hr => inside r ((hA.2.2.2 n).2 r hl hr)⟩⟩

theorem secant_neg_compute (f : Rat → RealRaw) {a b : Rat} (hab : a<b) (n : Nat) :
    (secant (fun r => -(f r)) a b).compute n =
      (-(secant f a b)).compute n := by
  have hp : 0<b-a := by grind only
  have hi : 0≤1/(b-a) := by
    rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr hp)
  change RealRaw.scaleRatCompute (1/(b-a))
    (RealRaw.sub (RealRaw.neg (f b)) (RealRaw.neg (f a))) n =
    RealRaw.negCompute (RealRaw.scaleRat (1/(b-a)) (RealRaw.sub (f b) (f a))) n
  simp only [RealRaw.scaleRatCompute,RealRaw.scaleRat,RealRaw.sub,RealRaw.subCompute,
    RealRaw.neg,RealRaw.negCompute,if_pos hi]
  congr 1 <;> grind only


theorem HasDerivativeAt.negate {domain : Rat → Prop} {f : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d) : HasDerivativeAt domain (fun r => -(f r)) x (-d) := by
  refine ⟨h.1,RealRaw.neg_valid h.2.1,fun r hr => RealRaw.neg_valid (h.2.2.1 r hr),h.2.2.2.1,fun A hA => ?_⟩
  obtain ⟨hd,Q,n,m,hn,hm,hC,hCd,cover⟩ := h.2.2.2.2 A hA
  let R := fun n m => ({lo:=-(Q n m).hi,hi:=-(Q n m).lo} : QInterval)
  refine ⟨RealRaw.neg_valid hd,R,n,m,hn,hm,RealRaw.neg_valid hC,RealRaw.neg_equiv hCd,?_⟩
  rintro k y ⟨a,b,ha,hab,hb,rfl⟩
  have bound := cover k _ ⟨a,b,ha,hab,hb,rfl⟩
  constructor
  · intro i j
    have fact := bound.2 j 0
    change -(Q (n k) (m k)).hi≤((secant (fun r => -(f r)) a b).compute j).hi
    rw [secant_neg_compute f hab]
    change -(Q (n k) (m k)).hi≤-((secant f a b).compute j).lo
    exact Rat.neg_le_neg fact
  · intro i j
    have fact := bound.1 0 i
    change ((secant (fun r => -(f r)) a b).compute i).lo≤-(Q (n k) (m k)).lo
    rw [secant_neg_compute f hab]
    change -((secant f a b).compute i).hi≤-(Q (n k) (m k)).lo
    exact Rat.neg_le_neg fact

/-- Reversing real endpoints gives the same literal slope intervals. Thus
ordered pairs cover every nonzero real direction without an extra assumption. -/
theorem secant_swap_compute (f : Rat → RealRaw) {a b : Rat} (hab : a<b) (n : Nat) :
    (secant f b a).compute n=(secant f a b).compute n := by
  have hp : 0<b-a := by grind only
  have hc := Rat.inv_mul_cancel (b-a) (Rat.ne_of_gt hp)
  have hn : a-b≠0 := by grind only
  have hd := Rat.inv_mul_cancel (a-b) hn
  have he : 1/(a-b)=-(1/(b-a)) := by
    simp only [Rat.div_def,Rat.one_mul]
    grind only
  have hpos : 0<1/(b-a) := by
    rw [Rat.div_def,Rat.one_mul]; exact Rat.inv_pos.mpr hp
  have hneg : ¬0≤1/(a-b) := by rw [he]; grind only
  have hi := Rat.le_of_lt hpos
  change RealRaw.scaleRatCompute (1/(a-b)) (RealRaw.sub (f a) (f b)) n=
    RealRaw.scaleRatCompute (1/(b-a)) (RealRaw.sub (f b) (f a)) n
  simp only [RealRaw.scaleRatCompute,RealRaw.sub,RealRaw.subCompute,if_pos hi,if_neg hneg]
  rw [he]
  congr 1 <;> grind only

end ComputableAnalysis.RealSecantDerivative
