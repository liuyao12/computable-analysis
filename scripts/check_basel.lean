import Lean
import ComputableAnalysis.Basel.RealZeta

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
  let basel := ((projectClosure env ``ComputableAnalysis.Basel.eulerBasel).run {}).2
  let primes := ((projectClosure env ``ComputableAnalysis.Basel.prime_unbounded_of_piSquare_irrational).run {}).2
  for required in [``ComputableAnalysis.Basel.zeta_leibniz_square_budget,
      ``ComputableAnalysis.leibnizRaw_equiv_geom] do
    unless basel.contains required do throwError "Basel lost its finite comparison: {required}"
  for required in [``ComputableAnalysis.Basel.eulerBasel,
      ``ComputableAnalysis.Basel.EulerSieve.sieve_error,
      ``ComputableAnalysis.Basel.zetaTwo_equiv_finiteEulerProduct] do
    unless primes.contains required do throwError "Prime proof lost its analytic route: {required}"
  for forbidden in [``ComputableAnalysis.exists_basicPrime_gt,
      ``ComputableAnalysis.exists_basicPrime_not_mem_of_all_basicPrime] do
    if primes.contains forbidden then throwError "Prime proof uses Euclid's infinitude theorem: {forbidden}"
  for root in [``ComputableAnalysis.Basel.eulerBasel,
      ``ComputableAnalysis.Basel.prime_unbounded_of_piSquare_irrational,
      ``ComputableAnalysis.Basel.real_zeta_two_equiv_piSquaredOverSix] do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {root}"
    for name in axioms do
      if name.toString.startsWith "ComputableAnalysis.Basel." then
        throwError "New Basel axiom: {name}"
  logInfo "PASS: Basel comparison and Euler sieve occur in the elaborated proofs; no Euclidean infinitude shortcut or unfinished proof"

#print ComputableAnalysis.Basel.eulerBasel
#print ComputableAnalysis.Basel.prime_unbounded_of_piSquare_irrational
