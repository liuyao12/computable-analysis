import ComputableAnalysis.ModularForms.CMLatticeInverseFormula163

/-! Exact real coordinate formula for executable CM lattice points. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

theorem complexRaw_real_compute (u : QuadraticOrder163) (n : Nat) :
    u.complexRaw.realPart.compute n=
      {lo := (u.x:Rat)+(u.y:Rat)/2,hi := (u.x:Rat)+(u.y:Rat)/2} := by
  simp only [complexRaw,integerAffine,translate,cmPoint163,ComplexRaw.realPart,
    ComplexRaw.scaleRat,ComplexRaw.add,ComplexRaw.one,ComplexRaw.ofQComplex,
    ComplexRaw.imaginaryAxis_compute,QBox.scaleRat,QBox.add,QComplex.add,QComplex.one]
  simp only [if_pos (show (0:Rat)≤1/2 by decide +kernel)]
  split <;> congr 1 <;> grind

theorem complexRaw_real (u : QuadraticOrder163) :
    u.complexRaw.realPart.Equiv (RealRaw.ofRat ((u.x:Rat)+(u.y:Rat)/2)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  rw [complexRaw_real_compute]
  exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem normInverseRaw_real_compute (u : QuadraticOrder163) (n : Nat) :
    u.normInverseRaw.realPart.compute n=
      {lo := ((u.x:Rat)+(u.y:Rat)/2)/(norm u:Rat),
       hi := ((u.x:Rat)+(u.y:Rat)/2)/(norm u:Rat)} := by
  have he := complexRaw_real_compute (conjugate u) n
  have hlo := congrArg QInterval.lo he
  have hhi := congrArg QInterval.hi he
  change ((conjugate u).complexRaw.compute n).lo.re=
    ((u.x+u.y:Int):Rat)+((-u.y:Int):Rat)/2 at hlo
  change ((conjugate u).complexRaw.compute n).hi.re=
    ((u.x+u.y:Int):Rat)+((-u.y:Int):Rat)/2 at hhi
  simp only [normInverseRaw,ComplexRaw.realPart,ComplexRaw.scaleRat,QBox.scaleRat]
  split <;> simp only [hlo,hhi] <;> congr 1 <;> grind [Rat.div_def]

end ComputableAnalysis.ModularForms.QuadraticOrder163
