import ComputableAnalysis.RiemannHilbert.ScalarFiberTopology
import ComputableAnalysis.RiemannHilbert.DomainContinuity
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra

/-! Effective joint continuity of scalar and vector functions of a base
coordinate and fiber. Products use local bounds of the supplied values;
finite coordinate minima give vector moduli, including rank zero. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarFiberTopology
open ComplexRaw FunctionTheory DomainFunctions
variable {n m : Nat} {D : Point n → Prop}

structure ScalarContinuousOn (D : Point n → Prop) (f : ∀ p, D p → Scalar) where
  delta : ∀ a, D a → QPos → QPos
  estimate : ∀ a ha eps z hz, Near z a (delta a ha eps) →
    Small (sub (f z hz).val (f a ha).val) eps.val

structure VectorContinuousOn (D : Point n → Prop) (f : ∀ p, D p → Fiber m) where
  delta : ∀ a, D a → QPos → QPos
  estimate : ∀ a ha eps z hz, Near z a (delta a ha eps) → FiberTopology.Near (f z hz) (f a ha) eps

def ScalarContinuousOn.congr {f g : ∀ p, D p → Scalar}
    (hf : ScalarContinuousOn D f) (hfg : ∀ p hp, (f p hp).val.Equiv (g p hp).val) :
    ScalarContinuousOn D g where
  delta := hf.delta
  estimate a ha eps z hz hza := Small.congr
    (sub_valid (f z hz).property (f a ha).property) (sub_valid (g z hz).property (g a ha).property)
    (FunctionTheory.sub_congr (hfg z hz) (hfg a ha)) (hf.estimate a ha eps z hz hza)

def VectorContinuousOn.congr {f g : ∀ p, D p → Fiber m}
    (hf : VectorContinuousOn D f) (hfg : ∀ p hp, f p hp ≈ g p hp) : VectorContinuousOn D g where
  delta := hf.delta
  estimate a ha eps z hz hza := FiberTopology.Near.congr (hfg z hz) (hfg a ha) (hf.estimate a ha eps z hz hza)

def scalarConstant (c : Scalar) : ScalarContinuousOn D (fun _ _ => c) where
  delta _ _ eps := eps
  estimate _ _ eps _ _ _ := Small.congr (ofQComplex_valid _) (sub_valid c.property c.property)
    (equiv_symm (add_neg_equiv _ c.property)) (Small.zero (Rat.le_of_lt eps.property))

def baseContinuous : ScalarContinuousOn D (fun p _ => p.1) where
  delta _ _ eps := eps
  estimate _ _ _ _ _ hz := hz.1

def fiberCoordinateContinuous (i : Fin n) : ScalarContinuousOn D (fun p _ => Fiber.coordinate p.2 i) where
  delta _ _ eps := eps
  estimate _ _ _ _ _ hz := hz.2 i

def scalarLift {E : Scalar → Prop} (f : ∀ z, E z → Scalar) (hf : DomainFunctions.ContinuousOn E f) :
    ScalarContinuousOn (n := n) (fun p => E p.1) (fun p hp => f p.1 hp) where
  delta a ha := hf.delta a.1 ha
  estimate a ha eps z hz hza := hf.estimate a.1 ha eps z.1 hz hza.1

def scalarSumContinuous (f g : ∀ p, D p → Scalar)
    (hf : ScalarContinuousOn D f) (hg : ScalarContinuousOn D g) :
    ScalarContinuousOn D (fun p hp => scalarSum (f p hp) (g p hp)) where
  delta a ha eps := minRadius (hf.delta a ha (halfError eps)) (hg.delta a ha (halfError eps))
  estimate a ha eps z hz hza := by
    have hs := LocalODE.small_add
      (hf.estimate a ha (halfError eps) z hz (hza.mono (minRadius_left _ _)))
      (hg.estimate a ha (halfError eps) z hz (hza.mono (minRadius_right _ _)))
    have he : (halfError eps).val+(halfError eps).val=eps.val := by
      have h := halfError_identity eps
      grind only
    rw [he] at hs
    exact Small.congr (add_valid (sub_valid (f z hz).property (f a ha).property)
      (sub_valid (g z hz).property (g a ha).property))
      (sub_valid (scalarSum (f z hz) (g z hz)).property (scalarSum (f a ha) (g a ha)).property)
      (equiv_symm (scalarSum_difference _ _ _ _)) hs

def scalarProductContinuous (f g : ∀ p, D p → Scalar)
    (hf : ScalarContinuousOn D f) (hg : ScalarContinuousOn D g) :
    ScalarContinuousOn D (fun p hp => scalarProduct (f p hp) (g p hp)) where
  delta a ha eps := minRadius (hg.delta a ha unitError)
    (minRadius (hf.delta a ha (productLeftError eps (g a ha)))
      (hg.delta a ha (productRightError eps (f a ha))))
  estimate a ha eps z hz hza := by
    let alpha := productLeftError eps (g a ha)
    let beta := productRightError eps (f a ha)
    have h1 := hg.estimate a ha unitError z hz (hza.mono (minRadius_left _ _))
    have hrest := hza.mono (minRadius_right (hg.delta a ha unitError)
      (minRadius (hf.delta a ha alpha) (hg.delta a ha beta)))
    have hF := hf.estimate a ha alpha z hz (hrest.mono (minRadius_left _ _))
    have hG := hg.estimate a ha beta z hz (hrest.mono (minRadius_right _ _))
    have hsum := LocalODE.small_add (scalar_small (g a ha)) h1
    have hgz : Small (g z hz).val (scalarBound (g a ha)+1) := Small.congr
      (add_valid (g a ha).property (sub_valid (g z hz).property (g a ha).property)) (g z hz).property
      (SeriesLimitLaws.add_difference (g z hz).val (g a ha).val (g z hz).property (g a ha).property) hsum
    have hleft := Small.mul (sub_valid (f z hz).property (f a ha).property) (g z hz).property
      (Rat.le_of_lt alpha.property) (by have h := scalarBound_pos (g a ha); grind) hF hgz
    have hright := Small.mul (f a ha).property (sub_valid (g z hz).property (g a ha).property)
      (Rat.le_of_lt (scalarBound_pos _)) (Rat.le_of_lt beta.property) (scalar_small _) hG
    have hs := LocalODE.small_add hleft hright
    apply Small.congr
      (add_valid (mul_valid (sub_valid (f z hz).property (f a ha).property) (g z hz).property)
        (mul_valid (f a ha).property (sub_valid (g z hz).property (g a ha).property)))
      (sub_valid (scalarProduct (f z hz) (g z hz)).property (scalarProduct (f a ha) (g a ha)).property)
      (equiv_symm (scalarProduct_difference _ _ _ _))
    exact hs.mono (product_error_bound eps (f a ha) (g a ha))

def vectorOfCoordinates (f : ∀ p, D p → Fiber m)
    (hf : ∀ i : Fin m, ScalarContinuousOn D (fun p hp => Fiber.coordinate (f p hp) i)) :
    VectorContinuousOn D f where
  delta a ha eps := FiberTopology.finiteRadius (List.ofFn (fun i => (hf i).delta a ha eps))
  estimate a ha eps z hz hza i :=
    (hf i).estimate a ha eps z hz (hza.mono
      (FiberTopology.finiteRadius_le _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))

def productContinuous (f : ∀ p, D p → Scalar) (g : ∀ p, D p → Fiber m)
    (hf : ScalarContinuousOn D f) (hg : VectorContinuousOn D g) :
    ContinuousOn D (fun p hp => (f p hp,g p hp)) where
  delta a ha eps := minRadius (hf.delta a ha eps) (hg.delta a ha eps)
  estimate a ha eps z hz hza :=
    ⟨hf.estimate a ha eps z hz (hza.mono (minRadius_left _ _)),
      hg.estimate a ha eps z hz (hza.mono (minRadius_right _ _))⟩

def vectorIdentity : VectorContinuousOn D (fun p _ => p.2) where
  delta _ _ eps := eps
  estimate _ _ _ _ _ hz := hz.2

/-- A nonlinear scalar chart change, including reciprocal, acts continuously
on the product with the identity fiber map. -/
def baseChangeContinuous (f : DomainFunctions.Map) (hf : DomainFunctions.ContinuousOn f.domain f.eval) :
    ContinuousOn (n := n) (m := n) (fun p => f.domain p.1) (fun p hp => (f.eval p.1 hp,p.2)) :=
  productContinuous (n := n) (m := n) (fun p hp => f.eval p.1 hp) (fun p _ => p.2)
    (scalarLift (n := n) f.eval hf) (vectorIdentity (n := n))

theorem baseChange_preimage_isOpen (f : DomainFunctions.Map) (hD : ScalarTopology.IsOpen f.domain)
    (hf : DomainFunctions.ContinuousOn f.domain f.eval) (U : Point n → Prop) (hU : IsOpen U) :
    IsOpen (preimage (fun p : Point n => f.domain p.1) (fun p hp => (f.eval p.1 hp,p.2)) U) :=
  preimage_isOpen (n := n) (m := n) (fun p : Point n => f.domain p.1)
    (isOpen_base (n := n) f.domain hD) (fun p hp => (f.eval p.1 hp,p.2))
    (fun z w hz hw hzw => ⟨f.eval_congr z.1 w.1 hz hw hzw.1,hzw.2⟩) (baseChangeContinuous (n := n) f hf) U hU

end ComputableAnalysis.RiemannHilbert.ScalarFiberTopology
