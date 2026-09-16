import ComputableAnalysis.FiniteSampleCalculus

/-! Discrete summation by parts on a finite binary partition. The identities
are exact rational identities, before any limiting statement or derivative.
The remainder estimate uses local increment bounds but not the general FTC. -/
namespace ComputableAnalysis.FiniteSummationByParts
open ClosedArctanInverse MonotoneAverage RationalSampleLimits FiniteSampleCalculus

/-- Sum an expression attached to each leaf interval of a dyadic partition. -/
def cellSum (v : Rat → Rat → Rat) (a b : Rat) : Nat → Rat
  | 0 => v a b
  | d+1 => cellSum v a ((a+b)/2) d+cellSum v ((a+b)/2) b d

theorem cellSum_add (f g : Rat → Rat → Rat) (a b : Rat) (d : Nat) :
    cellSum (fun x y=>f x y+g x y) a b d=cellSum f a b d+cellSum g a b d := by
  induction d generalizing a b with
  | zero => rfl
  | succ d ih =>
    simp only [cellSum,ih]
    grind only

theorem cellSum_sub (f g : Rat → Rat → Rat) (a b : Rat) (d : Nat) :
    cellSum (fun x y=>f x y-g x y) a b d=cellSum f a b d-cellSum g a b d := by
  induction d generalizing a b with
  | zero => rfl
  | succ d ih =>
    simp only [cellSum,ih]
    grind only

theorem rectangle_identity (f : Rat → Rat) (a b : Rat) (d : Nat) :
    cellSum (fun x y=>(y-x)*f x) a b d=(b-a)*left f a b d := by
  induction d generalizing a b with
  | zero => rfl
  | succ d ih =>
    simp only [cellSum,left,ih,Rat.div_def]
    grind only

/-- The product identity, including the quadratic cross-increment term. -/
theorem product_identity (f g : Rat → Rat) (a b : Rat) (d : Nat) :
    cellSum (fun x y=>f x*(g y-g x)+g x*(f y-f x)+(f y-f x)*(g y-g x)) a b d =
      f b*g b-f a*g a := by
  induction d generalizing a b with
  | zero =>
    change f a*(g b-g a)+g a*(f b-f a)+(f b-f a)*(g b-g a)=_
    grind only
  | succ d ih =>
    simp only [cellSum,ih]
    grind only

/-- Accumulate an eventual quadratic cell error on a FIXED finite partition.
No integral object or fundamental theorem is used. -/
theorem quadratic_accumulation (v : Rat → Rat → Nat → Rat) (K : Rat)
    (bound : ∀ a b, Unit a → Unit b → a<b →
      ∃ N, ∀ q, N≤q → qabs (v a b q)≤K*(b-a)*(b-a))
    (d : Nat) {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b) :
    ∃ N, ∀ q, N≤q → qabs (cellSum (fun x y=>v x y q) a b d)≤K*(b-a)*(b-a)*meshRadius d := by
  induction d generalizing a b with
  | zero =>
    obtain ⟨N,hN⟩:=bound a b ha hb hab
    refine ⟨N,fun q hq=>?_⟩
    rw [show meshRadius 0=(1:Rat) by decide +kernel,Rat.mul_one]
    exact hN q hq
  | succ d ih =>
    let m : Rat := (a+b)/2
    have hm : Unit m := midpoint_unit ha hb
    have ham : a<m := by dsimp [m];simp only [Rat.div_def];grind
    have hmb : m<b := by dsimp [m];simp only [Rat.div_def];grind
    obtain ⟨N,hN⟩:=ih ha hm ham
    obtain ⟨M,hM⟩:=ih hm hb hmb
    refine ⟨max N M,fun q hq=>?_⟩
    have h1:=hN q (by omega);have h2:=hM q (by omega)
    have ht:=qabs_add_le (cellSum (fun x y=>v x y q) a m d) (cellSum (fun x y=>v x y q) m b d)
    change qabs (cellSum (fun x y=>v x y q) a m d+cellSum (fun x y=>v x y q) m b d)≤_
    have he : meshRadius (d+1)=meshRadius d/2 := by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev]
      exact Rat.mul_comm _ _
    rw [he]
    dsimp [m] at h1 h2
    simp only [Rat.div_def] at h1 h2 ⊢
    grind only

def errorConstant {F D G E : SampleFunction} (f : Model F D) (g : Model G E) : Rat :=
  f.valueBound*g.errorBound+g.valueBound*f.errorBound+
    (f.slopeBound+f.errorBound)*(g.slopeBound+g.errorBound)

theorem errorConstant_nonneg {F D G E : SampleFunction} (f : Model F D) (g : Model G E) :
    0≤errorConstant f g :=
  Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg f.valueBound_nonneg g.errorBound_nonneg)
    (Rat.mul_nonneg g.valueBound_nonneg f.errorBound_nonneg))
    (Rat.mul_nonneg (Rat.add_nonneg f.slopeBound_nonneg f.errorBound_nonneg)
      (Rat.add_nonneg g.slopeBound_nonneg g.errorBound_nonneg))

/-- Direct finite summation by parts, not application of a product-primitive FTC.
The first two errors come from replacing increments by slope samples; the third
is the exact cross-increment term in the discrete product identity. -/
theorem finite_product_estimate {F D G E : SampleFunction} (f : Model F D) (g : Model G E)
    (d : Nat) {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b) :
    ∃ N, ∀ q, N≤q →
      qabs (F b q*G b q-F a q*G a q-
        (b-a)*left (fun x=>F x q*E x q+G x q*D x q) a b d) ≤
          errorConstant f g*(b-a)*(b-a)*meshRadius d := by
  let v := fun (x y:Rat) (q:Nat)=>
    F x q*(G y q-G x q-(y-x)*E x q)+
    G x q*(F y q-F x q-(y-x)*D x q)+
    (F y q-F x q)*(G y q-G x q)
  have hlocal : ∀ x y, Unit x → Unit y → x<y →
      ∃ N,∀q,N≤q→qabs (v x y q)≤errorConstant f g*(y-x)*(y-x) := by
    intro x y hx hy hxy
    obtain ⟨N,hN⟩:=f.local_error x y hx hy hxy
    obtain ⟨M,hM⟩:=g.local_error x y hx hy hxy
    obtain ⟨A,hA⟩:=f.increment_eventual x y hx hy hxy
    obtain ⟨B,hB⟩:=g.increment_eventual x y hx hy hxy
    refine ⟨max (max N M) (max A B),fun q hq=>?_⟩
    have h1:=mul_abs_bound f.valueBound_nonneg (f.value x q hx) (hM q (by omega))
    have h2:=mul_abs_bound g.valueBound_nonneg (g.value x q hx) (hN q (by omega))
    have hh : 0≤y-x := by grind
    have h3:=mul_abs_bound (Rat.mul_nonneg hh (Rat.add_nonneg f.slopeBound_nonneg f.errorBound_nonneg))
      (hA q (by omega)) (hB q (by omega))
    have ht1:=qabs_add_le (F x q*(G y q-G x q-(y-x)*E x q)) (G x q*(F y q-F x q-(y-x)*D x q))
    have ht2:=qabs_add_le
      (F x q*(G y q-G x q-(y-x)*E x q)+G x q*(F y q-F x q-(y-x)*D x q))
      ((F y q-F x q)*(G y q-G x q))
    dsimp [v,errorConstant]
    grind only
  obtain ⟨N,hN⟩:=quadratic_accumulation v (errorConstant f g) hlocal d ha hb hab
  refine ⟨N,fun q hq=>?_⟩
  have he : (fun x y=>v x y q)=(fun x y=>
      (F x q*(G y q-G x q)+G x q*(F y q-F x q)+(F y q-F x q)*(G y q-G x q))-
      (y-x)*(F x q*E x q+G x q*D x q)) := by
    funext x y;dsimp [v];grind only
  have h:=hN q hq
  rw [he,cellSum_sub,product_identity,rectangle_identity] at h
  exact h

/-- Combine two discrete integration-by-parts estimates and a separately proved
mesh comparison for the chosen sequence. No Model for the composite primitive
is built, and no general FTC theorem is invoked. -/
theorem two_products_close {F D G E H U V W : SampleFunction}
    (f : Model F D) (g : Model G E) (h : Model H U) (v : Model V W)
    (α β : Nat → Rat) (A B : Rat) (ha : 0≤A) (hb : 0≤B)
    (hα : Bounded α A) (hβ : Bounded β B)
    (I : Nat → Rat) (K : Rat) (hK : 0≤K)
    (mesh : ∀ d q, d≤q → qabs (I q-left (fun x=>
      α q*(F x q*E x q+G x q*D x q)-β q*(H x q*W x q+V x q*U x q)) 0 1 d)≤K*meshRadius d) :
    Close I (fun q=>α q*(F 1 q*G 1 q-F 0 q*G 0 q)-β q*(H 1 q*V 1 q-H 0 q*V 0 q)) := by
  let T := A*errorConstant f g+B*errorConstant h v+K
  have hT : 0≤T := Rat.add_nonneg
    (Rat.add_nonneg (Rat.mul_nonneg ha (errorConstant_nonneg f g))
      (Rat.mul_nonneg hb (errorConstant_nonneg h v))) hK
  have small : Small (fun d=>T*meshRadius d) := small_of_geometric_bound T hT (fun d=>by
    rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hT (Rat.le_of_lt (meshRadius_pos d)))];exact Rat.le_refl)
  intro eps
  obtain ⟨d,hd⟩:=small eps
  obtain ⟨N,hN⟩:=finite_product_estimate f g d (a:=0) (b:=1)
    ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide)
  obtain ⟨M,hM⟩:=finite_product_estimate h v d (a:=0) (b:=1)
    ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide)
  refine ⟨max d (max N M),fun q hq=>?_⟩
  have h1:=hN q (by omega);have h2:=hM q (by omega)
  have he : (1:Rat)-0=1 := by decide +kernel
  rw [he,Rat.mul_one,Rat.mul_one,Rat.one_mul] at h1 h2
  have ha1:=mul_abs_bound ha (hα q) h1
  have hb1:=mul_abs_bound hb (hβ q) h2
  have ht:=qabs_sub_le
    (α q*(F 1 q*G 1 q-F 0 q*G 0 q-left (fun x=>F x q*E x q+G x q*D x q) 0 1 d))
    (β q*(H 1 q*V 1 q-H 0 q*V 0 q-left (fun x=>H x q*W x q+V x q*U x q) 0 1 d))
  have hmesh:=mesh d q (by omega)
  rw [left_sub,left_mul,left_mul] at hmesh
  have htri:=qabs_sub_le
    (I q-(α q*left (fun x=>F x q*E x q+G x q*D x q) 0 1 d-
      β q*left (fun x=>H x q*W x q+V x q*U x q) 0 1 d))
    (α q*(F 1 q*G 1 q-F 0 q*G 0 q-left (fun x=>F x q*E x q+G x q*D x q) 0 1 d)-
      β q*(H 1 q*V 1 q-H 0 q*V 0 q-left (fun x=>H x q*W x q+V x q*U x q) 0 1 d))
  have halgebra : I q-(α q*left (fun x=>F x q*E x q+G x q*D x q) 0 1 d-
      β q*left (fun x=>H x q*W x q+V x q*U x q) 0 1 d)-
    (α q*(F 1 q*G 1 q-F 0 q*G 0 q-left (fun x=>F x q*E x q+G x q*D x q) 0 1 d)-
      β q*(H 1 q*V 1 q-H 0 q*V 0 q-left (fun x=>H x q*W x q+V x q*U x q) 0 1 d)) =
    I q-(α q*(F 1 q*G 1 q-F 0 q*G 0 q)-β q*(H 1 q*V 1 q-H 0 q*V 0 q)) := by grind only
  rw [halgebra] at htri
  have hlast:=hd d (Nat.le_refl d)
  have hpos:=self_le_qabs (T*meshRadius d)
  dsimp [T] at hpos hlast
  grind only

end ComputableAnalysis.FiniteSummationByParts
