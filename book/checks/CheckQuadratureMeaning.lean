import ComputableAnalysis.QuadratureAdapters

/-! Small permanent regressions for specification defects, not an exercise
catalogue. The permissive legacy records stay available for compatibility;
new mathematical clients require the additional semantic certificate. -/
open ComputableAnalysis ComputableAnalysis.Quadrature ComputableAnalysis.TaggedQuadrature

example (F : FunctionOnInterval) : Integral.ConstructionFor F :=
  ⟨(RealRaw.ofRat 0).compute,RealRaw.ofRat_valid 0⟩

private def coarseRaw : Integral.Raw :=
  Integral.algorithm (RealFunRaw.exact id) 0 1 (fun _ => {subdivisions:=1,evalPrecision:=0})

private theorem coarse_compute (n : Nat) : coarseRaw.compute n = {lo:=0,hi:=0} := by
  simp [coarseRaw,Integral.Raw.compute,Integral.algorithm,riemannLeftInterval,
    RealFunRaw.exact,leftPoint,mesh,List.range_succ]
  decide +kernel

private def coarse : Integral.Construction (RealFunRaw.exact id) 0 1 where
  plan := fun _ => {subdivisions:=1,evalPrecision:=0}
  certificate := Integral.Certificate.ofValid (by
    change RealRaw.ValidCompute coarseRaw.compute
    have he : coarseRaw.compute=(RealRaw.ofRat 0).compute := funext coarse_compute
    rw [he]
    exact RealRaw.ofRat_valid 0)

example (n : Nat) :
    (Integral.integral (RealFunRaw.exact id) 0 1 coarse).compute n = {lo:=0,hi:=0} := coarse_compute n

/-- The new certificate cannot certify the old one-cell zero computation as
an integral of x. It must also agree with midpoint-tagged sums. -/
example : ¬ Nonempty (Certificate (fun x => RealRaw.ofRat x) 0 1 (RealRaw.ofRat 0)) := by
  rintro ⟨h⟩
  have he := h.value_of_exact_rule (fun x:Rat => x)
    (fun x _ _ => RealRaw.equiv_refl _ (RealRaw.ofRat_valid x)) midpointTag (1/2)
    (by
      intro d
      have hh := midpoint_affine 1 0 0 1 d
      simpa only [Rat.one_mul,Rat.add_zero,Rat.zero_add,id,show (1:Rat)-0=1 by decide +kernel] using hh)
  have ho := (RealRaw.compareAt_overlap_iff _ _ 0 0).1 (he 0)
  change (0:Rat) ≤ 1/2 ∧ (1:Rat)/2 ≤ 0 at ho
  have hn : ¬ ((1:Rat)/2 ≤ 0) := by decide +kernel
  exact hn ho.2

example : ¬ Nonempty (Certificate (fun _ => RealRaw.ofRat 1) 0 1 (RealRaw.ofRat 0)) := by
  rintro ⟨h⟩
  have he := h.equiv (constant 1 0 1 (by decide))
  have ho := (RealRaw.compareAt_overlap_iff _ _ 0 0).1 (he 0)
  change (0:Rat) ≤ (1-0)*1 ∧ (1-0)*1 ≤ 0 at ho
  rw [show (1-0)*(1:Rat)=1 by decide +kernel] at ho
  have hn : ¬ ((1:Rat) ≤ 0) := by decide +kernel
  exact hn ho.2

#eval IO.println "PASS: legacy permissiveness exposed; both false quadratures rejected by the new certificate"
