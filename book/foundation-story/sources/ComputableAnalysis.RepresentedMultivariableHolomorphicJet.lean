import ComputableAnalysis.RepresentedHolomorphicJetAlgebra

/-!
# Represented multivariable complex first jets

A first jet in `dimension` variables consists of one represented complex value
and a represented complex partial derivative for every `Fin dimension`.
This is the finite-dimensional algebra needed by several-variable boundary
charts.  As with the one-variable represented jet, a concrete analytic chart
must additionally provide approximation certificates connecting these fields.
-/

namespace ComputableAnalysis
namespace RepresentedMultivariableHolomorphicJet

structure FirstJet (dimension : Nat) where
  value : ComplexRaw
  gradient : Fin dimension -> ComplexRaw

namespace FirstJet

def Valid {dimension : Nat} (jet : FirstJet dimension) : Prop :=
  jet.value.Valid /\ forall i, (jet.gradient i).Valid

def Equiv {dimension : Nat} (left right : FirstJet dimension) : Prop :=
  left.value.Equiv right.value /\
    forall i, (left.gradient i).Equiv (right.gradient i)

theorem equiv_refl {dimension : Nat} (jet : FirstJet dimension)
    (hjet : jet.Valid) : jet.Equiv jet :=
  ⟨ComplexRaw.equiv_refl jet.value hjet.1,
    fun i => ComplexRaw.equiv_refl (jet.gradient i) (hjet.2 i)⟩

theorem equiv_symm {dimension : Nat} {left right : FirstJet dimension}
    (h : left.Equiv right) : right.Equiv left :=
  ⟨ComplexRaw.equiv_symm h.1, fun i => ComplexRaw.equiv_symm (h.2 i)⟩

theorem equiv_trans {dimension : Nat}
    {left middle right : FirstJet dimension}
    (hleft : left.Valid) (hmiddle : middle.Valid) (hright : right.Valid)
    (hlm : left.Equiv middle) (hmr : middle.Equiv right) :
    left.Equiv right :=
  ⟨ComplexRaw.equiv_trans hleft.1 hmiddle.1 hright.1 hlm.1 hmr.1,
    fun i => ComplexRaw.equiv_trans (hleft.2 i) (hmiddle.2 i)
      (hright.2 i) (hlm.2 i) (hmr.2 i)⟩

def constant {dimension : Nat} (value : QComplex) : FirstJet dimension where
  value := ComplexRaw.ofQComplex value
  gradient := fun _ => ComplexRaw.zero

/-- A represented constant, retaining an arbitrary valid `ComplexRaw` value. -/
def constantRaw {dimension : Nat} (value : ComplexRaw) : FirstJet dimension where
  value := value
  gradient := fun _ => ComplexRaw.zero

/-- The selected coordinate projection on a represented input vector. -/
def coordinate {dimension : Nat} (input : Fin dimension -> ComplexRaw)
    (selected : Fin dimension) : FirstJet dimension where
  value := input selected
  gradient := fun i =>
    if i = selected then ComplexRaw.one else ComplexRaw.zero

def neg {dimension : Nat} (jet : FirstJet dimension) : FirstJet dimension where
  value := ComplexRaw.neg jet.value
  gradient := fun i => ComplexRaw.neg (jet.gradient i)

def add {dimension : Nat} (left right : FirstJet dimension) :
    FirstJet dimension where
  value := ComplexRaw.add left.value right.value
  gradient := fun i => ComplexRaw.add (left.gradient i) (right.gradient i)

def scaleRat {dimension : Nat} (scalar : Rat) (jet : FirstJet dimension) :
    FirstJet dimension where
  value := ComplexRaw.scaleRat scalar jet.value
  gradient := fun i => ComplexRaw.scaleRat scalar (jet.gradient i)

/-- Componentwise represented product rule. -/
def mul {dimension : Nat} (left right : FirstJet dimension) :
    FirstJet dimension where
  value := ComplexRaw.mul left.value right.value
  gradient := fun i => ComplexRaw.add
    (ComplexRaw.mul (left.gradient i) right.value)
    (ComplexRaw.mul left.value (right.gradient i))

/-- Compose a scalar one-variable jet, already evaluated at `inner.value`,
with a multivariable inner jet.  Agreement of the evaluation points belongs
to the surrounding chart certificate. -/
def composeScalar {dimension : Nat}
    (outer : RepresentedHolomorphicJet.FirstJet)
    (inner : FirstJet dimension) : FirstJet dimension where
  value := outer.value
  gradient := fun i => ComplexRaw.mul outer.derivative (inner.gradient i)

/-- Natural powers, computed by the represented product rule. -/
def powNat {dimension : Nat} (jet : FirstJet dimension) : Nat ->
    FirstJet dimension
  | 0 => constant QComplex.one
  | exponent + 1 => mul jet (powNat jet exponent)

@[simp] theorem powNat_zero {dimension : Nat} (jet : FirstJet dimension) :
    powNat jet 0 = constant QComplex.one := rfl

@[simp] theorem powNat_succ {dimension : Nat} (jet : FirstJet dimension)
    (exponent : Nat) :
    powNat jet (exponent + 1) = mul jet (powNat jet exponent) := rfl

theorem constant_valid {dimension : Nat} (value : QComplex) :
    (constant value : FirstJet dimension).Valid :=
  ⟨ComplexRaw.ofQComplex_valid value,
    fun _ => ComplexRaw.ofQComplex_valid QComplex.zero⟩

theorem constantRaw_valid {dimension : Nat} {value : ComplexRaw}
    (hvalue : value.Valid) : (constantRaw value : FirstJet dimension).Valid :=
  ⟨hvalue, fun _ => ComplexRaw.ofQComplex_valid QComplex.zero⟩

theorem constantRaw_equiv {dimension : Nat} {left right : ComplexRaw}
    (h : left.Equiv right) :
    (constantRaw left : FirstJet dimension).Equiv (constantRaw right) :=
  ⟨h, fun _ => ComplexRaw.equiv_refl ComplexRaw.zero
    (ComplexRaw.ofQComplex_valid QComplex.zero)⟩

theorem coordinate_valid {dimension : Nat}
    (input : Fin dimension -> ComplexRaw)
    (hinput : forall i, (input i).Valid) (selected : Fin dimension) :
    (coordinate input selected).Valid := by
  constructor
  · exact hinput selected
  · intro i
    change (if i = selected then ComplexRaw.one else ComplexRaw.zero).Valid
    split <;> exact ComplexRaw.ofQComplex_valid _

theorem neg_valid {dimension : Nat} {jet : FirstJet dimension}
    (hjet : jet.Valid) : (neg jet).Valid :=
  ⟨ComplexRaw.neg_valid hjet.1,
    fun i => ComplexRaw.neg_valid (hjet.2 i)⟩

theorem add_valid {dimension : Nat} {left right : FirstJet dimension}
    (hleft : left.Valid) (hright : right.Valid) :
    (add left right).Valid :=
  ⟨ComplexRaw.add_valid hleft.1 hright.1,
    fun i => ComplexRaw.add_valid (hleft.2 i) (hright.2 i)⟩

theorem scaleRat_valid {dimension : Nat} (scalar : Rat)
    {jet : FirstJet dimension} (hjet : jet.Valid) :
    (scaleRat scalar jet).Valid :=
  ⟨ComplexRaw.scaleRat_valid hjet.1,
    fun i => ComplexRaw.scaleRat_valid (hjet.2 i)⟩

theorem mul_valid {dimension : Nat} {left right : FirstJet dimension}
    (hleft : left.Valid) (hright : right.Valid) :
    (mul left right).Valid := by
  constructor
  · exact ComplexRaw.mul_valid hleft.1 hright.1
  · intro i
    exact ComplexRaw.add_valid
      (ComplexRaw.mul_valid (hleft.2 i) hright.1)
      (ComplexRaw.mul_valid hleft.1 (hright.2 i))

theorem composeScalar_valid {dimension : Nat}
    {outer : RepresentedHolomorphicJet.FirstJet}
    {inner : FirstJet dimension} (houter : outer.Valid)
    (hinner : inner.Valid) : (composeScalar outer inner).Valid :=
  ⟨houter.1, fun i => ComplexRaw.mul_valid houter.2 (hinner.2 i)⟩

theorem powNat_valid {dimension : Nat} {jet : FirstJet dimension}
    (hjet : jet.Valid) : forall exponent, (powNat jet exponent).Valid
  | 0 => constant_valid QComplex.one
  | exponent + 1 => mul_valid hjet (powNat_valid hjet exponent)

theorem neg_equiv {dimension : Nat} {left right : FirstJet dimension}
    (h : left.Equiv right) : (neg left).Equiv (neg right) :=
  ⟨ComplexRaw.neg_equiv h.1, fun i => ComplexRaw.neg_equiv (h.2 i)⟩

theorem add_equiv {dimension : Nat}
    {left left' right right' : FirstJet dimension}
    (hleft : left.Equiv left') (hright : right.Equiv right') :
    (add left right).Equiv (add left' right') :=
  ⟨ComplexRaw.add_equiv hleft.1 hright.1,
    fun i => ComplexRaw.add_equiv (hleft.2 i) (hright.2 i)⟩

theorem scaleRat_equiv {dimension : Nat} (scalar : Rat)
    {left right : FirstJet dimension} (h : left.Equiv right) :
    (scaleRat scalar left).Equiv (scaleRat scalar right) :=
  ⟨ComplexRaw.scaleRat_equiv h.1,
    fun i => ComplexRaw.scaleRat_equiv (h.2 i)⟩

theorem mul_equiv {dimension : Nat}
    {left left' right right' : FirstJet dimension}
    (hl : left.Valid) (hl' : left'.Valid)
    (hr : right.Valid) (hr' : right'.Valid)
    (hleft : left.Equiv left') (hright : right.Equiv right') :
    (mul left right).Equiv (mul left' right') := by
  constructor
  · exact ComplexRaw.mul_equiv hl.1 hl'.1 hr.1 hr'.1 hleft.1 hright.1
  · intro i
    apply ComplexRaw.add_equiv
    · exact ComplexRaw.mul_equiv (hl.2 i) (hl'.2 i) hr.1 hr'.1
        (hleft.2 i) hright.1
    · exact ComplexRaw.mul_equiv hl.1 hl'.1 (hr.2 i) (hr'.2 i)
        hleft.1 (hright.2 i)

theorem composeScalar_equiv {dimension : Nat}
    {outer outer' : RepresentedHolomorphicJet.FirstJet}
    {inner inner' : FirstJet dimension}
    (ho : outer.Valid) (ho' : outer'.Valid)
    (hi : inner.Valid) (hi' : inner'.Valid)
    (houter : outer.Equiv outer') (hinner : inner.Equiv inner') :
    (composeScalar outer inner).Equiv (composeScalar outer' inner') :=
  ⟨houter.1, fun i => ComplexRaw.mul_equiv ho.2 ho'.2
    (hi.2 i) (hi'.2 i) houter.2 (hinner.2 i)⟩

theorem powNat_equiv {dimension : Nat} {left right : FirstJet dimension}
    (hleft : left.Valid) (hright : right.Valid) (h : left.Equiv right) :
    forall exponent, (powNat left exponent).Equiv (powNat right exponent)
  | 0 => equiv_refl (constant QComplex.one) (constant_valid QComplex.one)
  | exponent + 1 => mul_equiv hleft hright
      (powNat_valid hleft exponent) (powNat_valid hright exponent)
      h (powNat_equiv hleft hright h exponent)

/-! ## Finite sums and the radius-square chart -/

def rawSum : List ComplexRaw -> ComplexRaw
  | [] => ComplexRaw.zero
  | value :: rest => ComplexRaw.add value (rawSum rest)

theorem rawSum_valid (values : List ComplexRaw)
    (hvalues : forall value, value ∈ values -> value.Valid) :
    (rawSum values).Valid := by
  induction values with
  | nil => exact ComplexRaw.ofQComplex_valid QComplex.zero
  | cons value rest ih =>
      apply ComplexRaw.add_valid
      · exact hvalues value (by simp)
      · apply ih
        intro item hitem
        exact hvalues item (by simp [hitem])

def radiusSquaredValue {dimension : Nat}
    (coordinates : Fin dimension -> ComplexRaw) : ComplexRaw :=
  rawSum ((List.ofFn coordinates).map fun coordinate =>
    ComplexRaw.mul coordinate coordinate)

theorem radiusSquaredValue_valid {dimension : Nat}
    (coordinates : Fin dimension -> ComplexRaw)
    (hcoordinates : forall i, (coordinates i).Valid) :
    (radiusSquaredValue coordinates).Valid := by
  apply rawSum_valid
  intro value hvalue
  simp only [List.mem_map] at hvalue
  obtain ⟨coordinate, hcoordinate, rfl⟩ := hvalue
  rw [List.mem_ofFn] at hcoordinate
  obtain ⟨i, rfl⟩ := hcoordinate
  exact ComplexRaw.mul_valid (hcoordinates i) (hcoordinates i)

/-- The represented polynomial chart `sum_i z_i^2`, with all of its partial
derivatives stored simultaneously. -/
def radiusSquared {dimension : Nat}
    (coordinates : Fin dimension -> ComplexRaw) : FirstJet dimension where
  value := radiusSquaredValue coordinates
  gradient := fun i => ComplexRaw.scaleRat 2 (coordinates i)

theorem radiusSquared_valid {dimension : Nat}
    (coordinates : Fin dimension -> ComplexRaw)
    (hcoordinates : forall i, (coordinates i).Valid) :
    (radiusSquared coordinates).Valid :=
  ⟨radiusSquaredValue_valid coordinates hcoordinates,
    fun i => ComplexRaw.scaleRat_valid (hcoordinates i)⟩

@[simp] theorem radiusSquared_partial {dimension : Nat}
    (coordinates : Fin dimension -> ComplexRaw) (i : Fin dimension) :
    (radiusSquared coordinates).gradient i =
      ComplexRaw.scaleRat 2 (coordinates i) := rfl

/-! ## Space-time coordinate charts -/

/-- Time is coordinate zero; spatial variables occupy the successor slots. -/
def timeCoordinate {spatialDimension : Nat} (time : ComplexRaw) :
    FirstJet (spatialDimension + 1) where
  value := time
  gradient := Fin.cases ComplexRaw.one (fun _ => ComplexRaw.zero)

theorem timeCoordinate_valid {spatialDimension : Nat} {time : ComplexRaw}
    (htime : time.Valid) :
    (timeCoordinate (spatialDimension := spatialDimension) time).Valid := by
  constructor
  · exact htime
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i <;>
      exact ComplexRaw.ofQComplex_valid _

@[simp] theorem timeCoordinate_partial_zero {spatialDimension : Nat}
    (time : ComplexRaw) :
    (timeCoordinate (spatialDimension := spatialDimension) time).gradient 0 =
      ComplexRaw.one := rfl

@[simp] theorem timeCoordinate_partial_succ {spatialDimension : Nat}
    (time : ComplexRaw) (i : Fin spatialDimension) :
    (timeCoordinate (spatialDimension := spatialDimension) time).gradient i.succ =
      ComplexRaw.zero := rfl

/-- The spatial polynomial `sum_i z_i^2`, regarded as a space-time chart
whose time partial is zero. -/
def spaceTimeRadiusSquared {spatialDimension : Nat}
    (space : Fin spatialDimension -> ComplexRaw) :
    FirstJet (spatialDimension + 1) where
  value := radiusSquaredValue space
  gradient := Fin.cases ComplexRaw.zero
    (fun i => ComplexRaw.scaleRat 2 (space i))

theorem spaceTimeRadiusSquared_valid {spatialDimension : Nat}
    (space : Fin spatialDimension -> ComplexRaw)
    (hspace : forall i, (space i).Valid) :
    (spaceTimeRadiusSquared space).Valid := by
  constructor
  · exact radiusSquaredValue_valid space hspace
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ComplexRaw.ofQComplex_valid QComplex.zero
    · exact ComplexRaw.scaleRat_valid (hspace j)

@[simp] theorem spaceTimeRadiusSquared_partial_zero
    {spatialDimension : Nat} (space : Fin spatialDimension -> ComplexRaw) :
    (spaceTimeRadiusSquared space).gradient 0 = ComplexRaw.zero := rfl

@[simp] theorem spaceTimeRadiusSquared_partial_succ
    {spatialDimension : Nat} (space : Fin spatialDimension -> ComplexRaw)
    (i : Fin spatialDimension) :
    (spaceTimeRadiusSquared space).gradient i.succ =
      ComplexRaw.scaleRat 2 (space i) := rfl

end FirstJet
end RepresentedMultivariableHolomorphicJet
end ComputableAnalysis
