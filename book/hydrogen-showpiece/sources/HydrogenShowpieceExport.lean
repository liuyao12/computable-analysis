import ComputableAnalysis.HydrogenSmallCouplingPredictions

/-! Checked interval data for the hydrogen showpiece Page. Couplings are
synthetic. Decimal presentation uses rational outward rounding; a finite
rational guard proves the final enclosure and its requested width. -/
namespace HydrogenShowpiece
open ComputableAnalysis ComputableCoefficient QuotientBridge HydrogenCoupling
set_option autoImplicit false
set_option maxHeartbeats 4000000

def rationalCoupling (u : Rat) (h0 : 0≤u) (h1 : u<1) : Coupling where
  squared := Real.ofRat u
  nonnegative := fun _ _ => h0
  le_one := fun _ _ => Rat.le_of_lt h1
  ne_one := by
    intro h
    have he := (RealRaw.compareAt_overlap_iff _ _ 0 0).1 (h 0)
    change u≤1 ∧ 1≤u at he
    grind only

def lower (r : Rat) : Rat := (((r.num*(1000000000:Int))/(r.den:Int) : Int):Rat)/1000000000
def rounded (I : QInterval) : QInterval := ⟨lower I.lo,lower I.hi+1/1000000000⟩

theorem contained (r : Value) (N : Nat) (Q : QInterval)
    (hL : Q.lo≤(r.real.compute N).lo) (hU : (r.real.compute N).hi≤Q.hi) :
    RawLimit.InInterval r.real.preferred Q := by
  constructor
  · intro i j
    change Q.lo≤(r.real.compute j).hi
    exact Rat.le_trans hL (RealRaw.le_refl r.real.preferred r.real.valid N j)
  · intro i j
    change (r.real.compute i).lo≤Q.hi
    exact Rat.le_trans (RealRaw.le_refl r.real.preferred r.real.valid i N) hU

/-- The returned interval has an actual enclosure role, not merely a
plausible decimal value. The fallback preserves every requested accuracy. -/
def enclosure (A : Coupling) (eps : QPos) :
    {Q : QInterval // RawLimit.InInterval (HydrogenCircularRatio.ratio A).real.preferred Q ∧ Q.width≤eps.val} := by
  let r := HydrogenCircularRatio.ratio A
  let tau : QPos := ⟨eps.val/4,by rw [Rat.div_def];exact Rat.mul_pos eps.property (by decide +kernel)⟩
  let N := widthStageFrom r.real tau 0
  let I := r.real.compute N
  let J := rounded I
  if h : J.lo≤I.lo ∧ I.hi≤J.hi ∧ J.width≤eps.val then
    exact ⟨J,contained r N J h.1 h.2.1,h.2.2⟩
  else
    have hw := (widthStageFrom_spec r.real tau 0).2
    have he := Rat.le_of_lt eps.property
    have ht : tau.val≤eps.val := by change eps.val/4≤eps.val;grind only [Rat.div_def]
    exact ⟨I,contained r N I Rat.le_refl Rat.le_refl,Rat.le_trans hw ht⟩

/-- The same displayed interval encloses the genuine positive-gap quotient
of the actual regular radial eigenstates. -/
theorem actual_role (A : Coupling) (hA : ¬A.squared.preferred.Equiv RealRaw.zero) (eps : QPos) :
    RawLimit.InInterval (HydrogenRegularGraphFineStructure.ratio A hA).real.preferred (enclosure A eps).val ∧
      (enclosure A eps).val.width≤eps.val := by
  have h := (enclosure A eps).property
  have he := HydrogenRegularGraphFineStructure.ratio_agreement A hA
  constructor
  · exact ⟨RealRaw.le_trans (HydrogenCircularRatio.ratio A).real.valid h.1.1
      (RealRaw.le_of_equiv (HydrogenCircularRatio.ratio A).real.valid (HydrogenRegularGraphFineStructure.ratio A hA).real.valid
        (RealRaw.equiv_symm he)),
      RealRaw.le_trans (HydrogenCircularRatio.ratio A).real.valid
        (RealRaw.le_of_equiv (HydrogenRegularGraphFineStructure.ratio A hA).real.valid (HydrogenCircularRatio.ratio A).real.valid he) h.1.2⟩
  · exact h.2

def run : IO Unit := do
  for d in ([64,32,16] : List Nat) do
    let alpha : Rat := 1/(d:Rat)
    let u := alpha*alpha
    if h : 0≤u ∧ u<1 then
      let A := rationalCoupling u h.1 h.2
      for p in ([10,20] : List Nat) do
        let e : Rat := 1/((2:Rat)^p)
        if he : 0<e then
          let I := (enclosure A ⟨e,he⟩).val
          unless decide (I.width≤e) do throw (IO.userError "requested interval width")
          IO.println s!"ENCLOSURE|{d}|{p}|{I.lo}|{I.hi}|{I.width}"
        else throw (IO.userError "positive requested accuracy")
    else throw (IO.userError "synthetic coupling domain")
  IO.println "HYDROGEN SHOWPIECE SIX CHECKED RATIO ENCLOSURES PASS"
  (← IO.getStdout).flush
end HydrogenShowpiece
#eval HydrogenShowpiece.run
