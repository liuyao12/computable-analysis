import ComputableAnalysis.ModularForms.PairedRiccatiUniformMidpointCycle

/-! Finite four-child sums with bounds derived from actual leaf samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def rectangleSubdivisionSum (f : (QInterval × QInterval) → Scalar)
    (J : QInterval × QInterval) : Nat → Scalar
  | 0 => f J
  | n+1 =>
    scalarSum
      (scalarSum (rectangleSubdivisionSum f (bisectRectangle J (false,false)) n)
        (rectangleSubdivisionSum f (bisectRectangle J (false,true)) n))
      (scalarSum (rectangleSubdivisionSum f (bisectRectangle J (true,false)) n)
        (rectangleSubdivisionSum f (bisectRectangle J (true,true)) n))

theorem rectangleSubdivisionSum_leaf_bound (f : (QInterval × QInterval) → Scalar)
    (J : QInterval × QInterval) (n : Nat) (E : Rat)
    (hleaf : ∀ choice : Nat → Bool × Bool, Small (f (rectangleBisection J choice n)).val E) :
    Small (rectangleSubdivisionSum f J n).val (((4^n:Nat):Rat)*E) := by
  induction n generalizing J with
  | zero =>
    have hb := hleaf (fun _ => (false,false))
    change Small (f J).val (1*E)
    rw [Rat.one_mul]
    exact hb
  | succ n ih =>
    have child (r : Bool × Bool) : ∀ choice : Nat → Bool × Bool,
        Small (f (rectangleBisection (bisectRectangle J r) choice n)).val E := by
      intro choice
      let extended : Nat → Bool × Bool := fun j => match j with
        | 0 => r
        | j+1 => choice j
      have hb := hleaf extended
      rw [rectangleBisection_shift] at hb
      exact hb
    have hb := LocalODE.small_add
      (LocalODE.small_add (ih (bisectRectangle J (false,false)) (child (false,false)))
        (ih (bisectRectangle J (false,true)) (child (false,true))))
      (LocalODE.small_add (ih (bisectRectangle J (true,false)) (child (true,false)))
        (ih (bisectRectangle J (true,true)) (child (true,true))))
    have he : (((4^n:Nat):Rat)*E+((4^n:Nat):Rat)*E)+
        (((4^n:Nat):Rat)*E+((4^n:Nat):Rat)*E)=((4^(n+1):Nat):Rat)*E := by
      rw [Nat.pow_succ,Rat.natCast_mul]
      change _=(((4^n:Nat):Rat)*4)*E
      grind only
    rw [he] at hb
    exact hb

theorem four_pow_half_square (n : Nat) :
    ((4^n:Nat):Rat)*((1:Rat)/2)^n*((1:Rat)/2)^n=1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [Nat.pow_succ,Rat.natCast_mul,Rat.pow_succ]
    change (((4^n:Nat):Rat)*4)*(((1:Rat)/2)^n*(1/2))*(((1:Rat)/2)^n*(1/2))=1
    grind only

def pairedRiccatiFullRectangleCycle (J : QInterval × QInterval) : Scalar :=
  ⟨scaleRat 2 (pairedRiccatiRectangleCycle J).val,
    scaleRat_valid (pairedRiccatiRectangleCycle J).property⟩

def pairedRiccatiSubdivisionSum (J : QInterval × QInterval) (n : Nat) : Scalar :=
  rectangleSubdivisionSum pairedRiccatiFullRectangleCycle J n

theorem pairedRiccatiSubdivisionSum_eventual_bound (eps W : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → Small (pairedRiccatiSubdivisionSum J n).val
      (64*eps.val*W.val*W.val) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_dyadic_midpoint_error eps W J hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  have hb := rectangleSubdivisionSum_leaf_bound pairedRiccatiFullRectangleCycle J n
    (2*(32*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)))
    (fun choice => LocalODE.small_scale (by decide +kernel : (0:Rat)≤2) (hN choice n hn))
  have hp := four_pow_half_square n
  have he : ((4^n:Nat):Rat)*(2*(32*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)))=
      64*eps.val*W.val*W.val := by grind only
  rw [he] at hb
  exact hb

theorem pairedRiccatiSubdivisionSum_converges_zero (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (pairedRiccatiSubdivisionSum J n).val eps.val := by
  let W : QPos := ⟨1+qabs J.1.width+qabs J.2.width,by
    have hx := qabs_nonneg J.1.width
    have hy := qabs_nonneg J.2.width
    grind only⟩
  have hx : J.1.width≤2*W.val := by
    have ha := self_le_qabs J.1.width
    have hb := qabs_nonneg J.1.width
    have hc := qabs_nonneg J.2.width
    change J.1.width≤2*(1+qabs J.1.width+qabs J.2.width)
    grind only
  have hy : J.2.width≤2*W.val := by
    have ha := self_le_qabs J.2.width
    have hb := qabs_nonneg J.1.width
    have hc := qabs_nonneg J.2.width
    change J.2.width≤2*(1+qabs J.1.width+qabs J.2.width)
    grind only
  have hD : 0<64*W.val*W.val :=
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) W.property) W.property
  let eta : QPos := ⟨eps.val/(64*W.val*W.val),by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hD)⟩
  obtain ⟨N,hN⟩ := pairedRiccatiSubdivisionSum_eventual_bound eta W J hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  have he : eta.val*(64*W.val*W.val)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt hD)
  have he' : 64*eta.val*W.val*W.val=eps.val := by grind only
  rw [he'] at hb
  exact hb

end ComputableAnalysis.ModularForms
