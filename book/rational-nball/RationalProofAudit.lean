import Lean

open Lean

namespace RationalProofAudit
private partial def collect (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n::rest =>
    if seen.contains n then collect env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => collect env rest seen
      | some ci =>
        let deps := ci.type.getUsedConstants.toList ++
          (ci.value?.map (fun v => v.getUsedConstants.toList)).getD []
        collect env (deps ++ rest) seen

def audit (env : Environment) (names : List Name) : Array Name :=
  (collect env names {}).toArray.qsort Name.lt
end RationalProofAudit
