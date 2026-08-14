import ComputableAnalysis.Pi

/-!
# A finite circle-area certificate

These exact stages instantiate the circle-area exhaustion algorithm used for
benchmark item 9.  They are finite rational enclosures; no completed area
or real-number limit is asserted.
-/

namespace ComputableAnalysis

theorem piCircleArea_stage_one :
    piCircleArea.compute 1 = { lo := (14 : Rat) / 5, hi := (10 : Rat) / 3 } := by
  native_decide

theorem piCircleArea_stage_two :
    piCircleArea.compute 2 =
      { lo := (6486 : Rat) / 2125, hi := (2209 : Rat) / 693 } := by
  native_decide

theorem piCircleArea_stage_three :
    piCircleArea.compute 3 =
      { lo := (12651380374 : Rat) / 4056239525,
        hi := (114904921 : Rat) / 36443330 } := by
  native_decide

theorem piCircleArea_stage_four :
    piCircleArea.compute 4 =
      { lo := (26847520708606911739248854 : Rat) /
          8561273512627116885963125,
        hi := (15907328719703769776177606573 : Rat) /
          5058889236263304767788678644 } := by
  native_decide

theorem piCircleArea_stage_five :
    piCircleArea.compute 5 =
      { lo := (88836690398467666807053136155498284855937807677283167219518038 : Rat) /
          28290363216629886444830237407839277995931814233972938954661525,
        hi := (472755409812085476026164753331750274157326092369227 : Rat) /
          150448759219208414900668611280479945848705484952920 } := by
  native_decide

end ComputableAnalysis
