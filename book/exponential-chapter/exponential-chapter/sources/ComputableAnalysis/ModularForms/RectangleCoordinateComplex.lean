import ComputableAnalysis.ModularForms.RationalRectangleCover
import ComputableAnalysis.ModularForms.LocalRectangleMidpointBound

/-! Valid complex interval names and local displacement from rectangle
coordinate names. No completed real or complex type is introduced. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory

def coordinateComplex (x y : RealRaw) : ComplexRaw where
  compute n := ⟨⟨(x.compute n).lo,(y.compute n).lo⟩,
    ⟨(x.compute n).hi,(y.compute n).hi⟩⟩

theorem coordinateComplex_valid (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) :
    (coordinateComplex x y).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨hx.1 n,hy.1 n⟩
  · intro n m hnm
    have hxn := hx.2.1 n m hnm
    have hyn := hy.2.1 n m hnm
    exact ⟨hxn.1,hxn.2.2,hyn.1,hyn.2.2⟩
  · intro eps
    obtain ⟨X,hX⟩ := hx.2.2 eps
    obtain ⟨Y,hY⟩ := hy.2.2 eps
    refine ⟨max X Y, ?_⟩
    intro n hn
    exact ⟨hX n (by omega),hY n (by omega)⟩

theorem coordinateComplex_neighborhood (x y : RealRaw) (q : QComplex) (r : Rat)
    (hxl : RealRaw.Le (RealRaw.ofRat (q.re-r)) x)
    (hxu : RealRaw.Le x (RealRaw.ofRat (q.re+r)))
    (hyl : RealRaw.Le (RealRaw.ofRat (q.im-r)) y)
    (hyu : RealRaw.Le y (RealRaw.ofRat (q.im+r))) :
    Small (sub (ofQComplex q) (coordinateComplex x y)) r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have hb := hxu m 0
    change (x.compute m).lo≤q.re+r at hb
    change -r≤q.re + -(x.compute m).lo
    grind only
  · intro n m
    have hb := hxl 0 n
    change q.re-r≤(x.compute n).hi at hb
    change q.re + -(x.compute n).hi≤r
    grind only
  · intro n m
    have hb := hyu m 0
    change (y.compute m).lo≤q.im+r at hb
    change -r≤q.im + -(y.compute m).lo
    grind only
  · intro n m
    have hb := hyl 0 n
    change q.im-r≤(y.compute n).hi at hb
    change q.im + -(y.compute n).hi≤r
    grind only

theorem rectangleNear_complex_displacement (J : QInterval × QInterval)
    (x y : RealRaw) (eps : QPos)
    (hx : intervalNear J.1 x eps) (hy : intervalNear J.2 y eps)
    (q : QComplex) (hq : J.1.lo≤q.re ∧ q.re≤J.1.hi ∧
      J.2.lo≤q.im ∧ q.im≤J.2.hi) :
    Small (sub (ofQComplex q) (coordinateComplex x y)) eps.val := by
  have hxr := hx q.re hq.1 hq.2.1
  have hyr := hy q.im hq.2.2.1 hq.2.2.2
  exact coordinateComplex_neighborhood x y q eps.val hxr.1 hxr.2 hyr.1 hyr.2

end ComputableAnalysis.ModularForms
