import Lean
import ComputableAnalysis.Continuation

open Lean Elab Command
open ComputableAnalysis FunctionTheory Continuation

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib dependency: {mod}"
  for name in [``Small.sub_triangle, ``AgreeAt.trans, ``AgreeAt.congrPoint,
      ``agreeAt_nearby, ``HasDerivativeAt.unique, ``HasDerivativeAt.congrMap,
      ``derivative_eq_of_agreeAt, ``LocalModels.holomorphic,
      ``Along.append_exists, ``Along.singleChart,
      ``homotopy_direct, ``Region.simplyConnectedOfConvex,
      ``Transport.homotopy_invariant, ``Transport.path_independent,
      ``Transport.reverse_left, ``Transport.section_parallel,
      ``Transport.parallel_unique_on_path, ``Transport.section_unique,
      ``Affine.coefficients_of_germ, ``Affine.endpoint_independent,
      ``GermSystem.run_along, ``GermSystem.terminal_germ_independent,
      ``GermSystem.terminal_value_independent, ``GermSystem.terminal_from_equal_germs,
      ``Affine.germSystem, ``Realization.map, ``Realization.holomorphic, ``Realization.unique,
      ``Affine.realized_holomorphic, ``Holomorphic.reflect, ``AgreeAt.reflect] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Quot.sound, ``Classical.choice].contains ax ||
          (ax.toString.startsWith "_private.ComputableAnalysis.Basic." &&
            (ax.toString.splitOn "._native.native_decide.").length > 1) do
        throwError "Unapproved axiom in {name}: {ax}"
    logInfo m!"AUDIT {name}: {axioms}"
  logInfo "PASS: continuation foundations; no Mathlib imports, unfinished proofs, or new axioms; legacy Basic native-decide certificates are explicit."

-- No rational restriction on base points or derivative values.
example (f : FunctionTheory.Map) (o : OpenDomain f) (a d e : ComplexRaw)
    (hd : HasDerivativeAt f a d) (he : HasDerivativeAt f a e) : d.Equiv e :=
  hd.unique o he

example (f g : Affine) (a : Point) (h : f.localFunction a ≈ g.localFunction a) :
    f.slope.Equiv g.slope ∧ f.intercept.Equiv g.intercept :=
  Affine.coefficients_of_germ a h

example (f : FunctionTheory.Map) (L : LocalModels f) : Holomorphic f := L.holomorphic

-- A directly executable polygonal route and affine endpoint computation.
def qpoint (z : QComplex) : wholePlane.Vertex :=
  ⟨⟨ComplexRaw.ofQComplex z,ComplexRaw.ofQComplex_valid z⟩,True.intro⟩
def a0 := qpoint ⟨0,0⟩
def a1 := qpoint ⟨1,0⟩
def a2 := qpoint ⟨1,1⟩
def route : Path wholePlane.Edge a0 a2 :=
  .cons (wholePlane.convex_edge wholePlane_convex a0 a1)
    (.cons (wholePlane.convex_edge wholePlane_convex a1 a2) (.nil a2))
def seed : Affine :=
  ⟨ComplexRaw.ofQComplex ⟨2,1⟩,ComplexRaw.ofQComplex ⟨1,-1⟩,
    ComplexRaw.ofQComplex_valid _,ComplexRaw.ofQComplex_valid _⟩
#guard route.length == 2
#guard (((Affine.transport wholePlane).run route seed).localFunction a2.val).value.compute 0 ==
  QBox.point ⟨2,2⟩
#eval (((Affine.transport wholePlane).run route seed).localFunction a2.val).value.compute 0

-- Actual holomorphic chart coverage, not merely a raw-value transport.
def seedChart : Chart := ⟨seed.chart,(seed.localFunction a0.val).holomorphic⟩
example : Along route (seedChart.at a0.val True.intro) (seedChart.at a2.val True.intro) :=
  Along.singleChart seedChart route (fun _ => True.intro) (fun _ _ _ _ => True.intro)

example : (((Affine.transport wholePlane).run route seed).localFunction a2.val).value.Equiv
    (((Affine.transport wholePlane).run
      ((wholePlane.simplyConnectedOfConvex wholePlane_convex).route a0 a2) seed).localFunction a2.val).value :=
  Affine.endpoint_independent wholePlane (wholePlane.simplyConnectedOfConvex wholePlane_convex) _ _ seed

-- Executable realizations and reflected charts; the imaginary sign matters.
#guard (seed.realized.eval (ComplexRaw.ofQComplex ⟨1,1⟩)).compute 0 == QBox.point ⟨2,2⟩
#guard (seed.chart.reflect.eval (ComplexRaw.ofQComplex ⟨1,1⟩)).compute 0 == QBox.point ⟨4,2⟩
example : Holomorphic seed.realized := seed.realized_holomorphic
example : Holomorphic seed.chart.reflect := (seed.localFunction a0.val).holomorphic.reflect
example (f : FunctionTheory.Map) (h : Holomorphic f) : Holomorphic f.reflect := h.reflect
