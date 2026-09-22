import Lean
import ComputableAnalysis.LeibnizPiTaylor

open Lean Elab Command

/-- Traverse elaborated types and proof bodies, including private project lemmas. -/
private partial def projectClosure (env : Environment) (name : Name) :
    StateM NameSet Unit := do
  if (← get).contains name then return
  if (name.toString.splitOn "ComputableAnalysis.").length ≤ 1 then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do projectClosure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do projectClosure env dep

run_cmd do
  let env ← getEnv
  let computational := ((projectClosure env ``ComputableAnalysis.pi_eq_leibniz).run {}).2
  let taylor := ((projectClosure env ``ComputableAnalysis.pi_eq_leibniz_taylor).run {}).2
  let mesh := ``ComputableAnalysis.PiProofs.leibnizEqualsRectangleRawAtOne_finiteRiemannBridge
  let ftc := ``ComputableAnalysis.Taylor.ArctanKernel.kernelPartial_exactCellOrder
  unless computational.contains mesh do throwError "Computational route lost its finite mesh bridge"
  if computational.contains ftc then throwError "Computational route depends on the FTC route"
  if computational.contains ``ComputableAnalysis.FinitePolynomial.SecantDerivativeBound ||
      computational.contains ``ComputableAnalysis.Integral.ExactCellOrderPreservation then
    throwError "Computational route uses a calculus certificate"
  unless taylor.contains ftc do throwError "Taylor route lost its polynomial FTC certificate"
  if taylor.contains mesh then throwError "Taylor route depends on the computational mesh bridge"
  for root in [``ComputableAnalysis.pi_eq_leibniz,
      ``ComputableAnalysis.pi_eq_leibniz_taylor,
      ``ComputableAnalysis.leibniz_stagewise_overlap,
      ``ComputableAnalysis.arctan_taylor_remainder_bound,
      ``ComputableAnalysis.arctan_taylor_integrated,
      ``ComputableAnalysis.leibnizRaw_valid,
      ``ComputableAnalysis.Taylor.ArctanKernel.finite_geometric_identity] do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof in {root}"
  let render := fun (s : NameSet) => String.intercalate "\n"
    ((s.toArray.qsort Name.lt).toList.map Name.toString)
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/leibniz-dependency-closure.txt"
    ("COMPUTATIONAL\n" ++ render computational ++ "\n\nTAYLOR / FTC\n" ++ render taylor ++ "\n")
  logInfo m!"PASS: distinct elaborated proof paths ({computational.toArray.size} / {taylor.toArray.size} project declarations). Full closure: tmp/leibniz-dependency-closure.txt"

#check ComputableAnalysis.leibnizPartial_succ
#check ComputableAnalysis.leibnizRaw_valid
#check ComputableAnalysis.leibnizRaw_width_le
#check ComputableAnalysis.leibniz_stagewise_overlap
#check ComputableAnalysis.pi_eq_leibniz
#check ComputableAnalysis.pi_leibniz_remainder
#check ComputableAnalysis.pi_eq_leibniz_taylor
#check ComputableAnalysis.Taylor.ArctanKernel.finite_geometric_identity
#check ComputableAnalysis.arctan_taylor_integrated
#check ComputableAnalysis.arctan_taylor_remainder_bound
#print axioms ComputableAnalysis.pi_eq_leibniz
#print axioms ComputableAnalysis.pi_eq_leibniz_taylor
#print axioms ComputableAnalysis.arctan_taylor_remainder_bound
#eval (List.range 5).map ComputableAnalysis.leibnizPartial
#eval (List.range 3).map (fun n => (ComputableAnalysis.leibnizRaw.compute n).display)
