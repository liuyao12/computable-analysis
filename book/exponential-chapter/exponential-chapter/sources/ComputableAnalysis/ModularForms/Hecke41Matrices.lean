import ComputableAnalysis.ModularForms.IntegerMatrices

/-! Explicit determinant-41 correspondence representatives and checked S/T reindexing. -/
namespace ComputableAnalysis.ModularForms

/-- Integer matrices used for finite modular correspondences. -/
structure CorrespondenceMatrix where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq

namespace CorrespondenceMatrix

def determinant (g : CorrespondenceMatrix) : Int := g.a*g.d-g.b*g.c

def multiply (g h : CorrespondenceMatrix) : CorrespondenceMatrix :=
  ⟨g.a*h.a+g.b*h.c,g.a*h.b+g.b*h.d,g.c*h.a+g.d*h.c,g.c*h.b+g.d*h.d⟩

def ofSL2Z (g : SL2Z) : CorrespondenceMatrix := ⟨g.a,g.b,g.c,g.d⟩

end CorrespondenceMatrix

/-- The 41 affine representatives and the one dilation representative. -/
def hecke41Representative (i : Fin 42) : CorrespondenceMatrix :=
  if i.val=41 then ⟨41,0,0,1⟩ else ⟨1,(i.val:Int),0,41⟩

/-- A literal modular negative-inverse computation for the nonzero residues. -/
def hecke41NegativeInverse (r : Nat) : Nat := (41-r^39%41)%41

private theorem negativeInverse_spec : ∀ r : Fin 41, r.val≠0 →
    0<hecke41NegativeInverse r.val ∧ hecke41NegativeInverse r.val<41 ∧
      ((r.val:Int)*(hecke41NegativeInverse r.val:Int)+1)%41=0 := by
  decide +kernel

/-- S exchanges zero and infinity, and acts by negative inversion on the other residues. -/
def hecke41SIndex (i : Fin 42) : Fin 42 :=
  Fin.ofNat 42 (if i.val=41 then 0 else if i.val=0 then 41 else hecke41NegativeInverse i.val)

/-- T cycles the 41 finite residues and fixes infinity. -/
def hecke41TIndex (i : Fin 42) : Fin 42 :=
  Fin.ofNat 42 (if i.val=41 then 41 else (i.val+1)%41)

/-- The inverse translation permutation. -/
def hecke41TInverseIndex (i : Fin 42) : Fin 42 :=
  Fin.ofNat 42 (if i.val=41 then 41 else (i.val+40)%41)

/-- The S reindexing is an involution on all 42 representatives. -/
theorem hecke41SIndex_involution : ∀ i : Fin 42, hecke41SIndex (hecke41SIndex i)=i := by
  decide +kernel

/-- Translation and its inverse are inverse permutations on all representatives. -/
theorem hecke41TIndex_inverse : ∀ i : Fin 42,
    hecke41TInverseIndex (hecke41TIndex i)=i ∧ hecke41TIndex (hecke41TInverseIndex i)=i := by
  decide +kernel

/-- The representative matrices all have determinant 41. -/
theorem hecke41Representative_determinant : ∀ i : Fin 42,
    (hecke41Representative i).determinant=41 := by
  decide +kernel

private def sWitnessMatrix (i : Fin 42) : CorrespondenceMatrix :=
  if i.val=41 ∨ i.val=0 then CorrespondenceMatrix.ofSL2Z SL2Z.S else
    let r : Int := i.val
    let s : Int := hecke41NegativeInverse i.val
    ⟨r,-((r*s+1)/41),41,-s⟩

private theorem sWitness_determinant : ∀ i : Fin 42, (sWitnessMatrix i).determinant=1 := by
  decide +kernel

/-- The explicit determinant-one S reindexing witness. -/
def hecke41SWitness (i : Fin 42) : SL2Z :=
  ⟨(sWitnessMatrix i).a,(sWitnessMatrix i).b,(sWitnessMatrix i).c,(sWitnessMatrix i).d,
    sWitness_determinant i⟩

/-- The explicit determinant-one T reindexing witness. -/
def hecke41TWitness (i : Fin 42) : SL2Z :=
  if i.val=41 then ⟨1,41,0,1,by decide +kernel⟩ else
    if i.val=40 then SL2Z.T else SL2Z.identity

/-- The actual S multiplication factors through the permuted representative and an SL2Z matrix. -/
theorem hecke41S_reindex : ∀ i : Fin 42,
    CorrespondenceMatrix.multiply (hecke41Representative i) (CorrespondenceMatrix.ofSL2Z SL2Z.S)=
      CorrespondenceMatrix.multiply (CorrespondenceMatrix.ofSL2Z (hecke41SWitness i))
        (hecke41Representative (hecke41SIndex i)) := by
  decide +kernel

/-- The actual T multiplication factors through the permuted representative and an SL2Z matrix. -/
theorem hecke41T_reindex : ∀ i : Fin 42,
    CorrespondenceMatrix.multiply (hecke41Representative i) (CorrespondenceMatrix.ofSL2Z SL2Z.T)=
      CorrespondenceMatrix.multiply (CorrespondenceMatrix.ofSL2Z (hecke41TWitness i))
        (hecke41Representative (hecke41TIndex i)) := by
  decide +kernel

end ComputableAnalysis.ModularForms
