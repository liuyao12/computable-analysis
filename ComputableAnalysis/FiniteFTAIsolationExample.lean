import ComputableAnalysis.FiniteFTAConcreteCertificate
import ComputableAnalysis.FiniteFTASubdivision

/-!
# A concrete finite FTA root-exclusion box

The polynomial `z^2 + 1` has roots at `i` and `-i`.  This example adds a
nontrivial rational box around the origin whose interval Horner image misses
zero, so the box is discarded by a finite root-exclusion certificate.  It is
an isolation-side certificate only: the exact roots remain supplied witnesses.
-/

namespace ComputableAnalysis

def finiteFTAZeroNeighborhood : QBox :=
  { lo := { re := -1 / 2, im := -1 / 2 },
    hi := { re := 1 / 2, im := 1 / 2 } }

theorem finiteFTAZeroNeighborhood_ordered :
    finiteFTAZeroNeighborhood.Ordered := by
  unfold finiteFTAZeroNeighborhood QBox.Ordered
  constructor <;> native_decide

def finiteFTAZeroNeighborhood_exclusion :
    QBox.FiniteRootExclusionCertificate finiteFTAQuadratic where
  domain := finiteFTAZeroNeighborhood
  boxes := [finiteFTAZeroNeighborhood]
  cover := by
    intro z hzlo hzhi
    exact ⟨finiteFTAZeroNeighborhood, by simp, hzlo, hzhi⟩
  misses_zero := by
    intro Z hZ
    have hZeq : Z = finiteFTAZeroNeighborhood := by simpa using hZ
    subst Z
    native_decide

theorem finiteFTAZeroNeighborhood_is_root_free :
    ∀ z : QComplex,
      finiteFTAZeroNeighborhood.lo <= z →
        z <= finiteFTAZeroNeighborhood.hi →
        CPoly.eval finiteFTAQuadratic z ≠ QComplex.zero := by
  intro z hzlo hzhi
  exact finiteFTAZeroNeighborhood_exclusion.no_root_in_domain hzlo hzhi

def finiteFTARootSearchDomain : QBox :=
  { lo := { re := -1, im := -1 },
    hi := { re := 1, im := 1 } }

theorem finiteFTARootSearchDomain_ordered :
    finiteFTARootSearchDomain.Ordered := by
  unfold finiteFTARootSearchDomain QBox.Ordered
  constructor <;> native_decide

theorem finiteFTAUpperRoot_survives_depth_two :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 2
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTAUpperRoot ∧ finiteFTAUpperRoot <= Z.hi ∧
      Z.width = 1 / 2 ∧ Z.height = 1 / 2 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTAUpperRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_upper_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 2 : Nat) : Rat) := hsize.1
      _ = 1 / 2 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 2 : Nat) : Rat) := hsize.2
      _ = 1 / 2 := by native_decide

theorem finiteFTALowerRoot_survives_depth_two :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 2
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTALowerRoot ∧ finiteFTALowerRoot <= Z.hi ∧
      Z.width = 1 / 2 ∧ Z.height = 1 / 2 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTALowerRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_lower_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 2 : Nat) : Rat) := hsize.1
      _ = 1 / 2 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 2 : Nat) : Rat) := hsize.2
      _ = 1 / 2 := by native_decide

theorem finiteFTAUpperRoot_survives_depth_three :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 3
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTAUpperRoot ∧ finiteFTAUpperRoot <= Z.hi ∧
      Z.width = 1 / 4 ∧ Z.height = 1 / 4 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTAUpperRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_upper_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 3 : Nat) : Rat) := hsize.1
      _ = 1 / 4 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 3 : Nat) : Rat) := hsize.2
      _ = 1 / 4 := by native_decide

theorem finiteFTALowerRoot_survives_depth_three :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 3
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTALowerRoot ∧ finiteFTALowerRoot <= Z.hi ∧
      Z.width = 1 / 4 ∧ Z.height = 1 / 4 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTALowerRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_lower_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 3 : Nat) : Rat) := hsize.1
      _ = 1 / 4 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 3 : Nat) : Rat) := hsize.2
      _ = 1 / 4 := by native_decide

theorem finiteFTAUpperRoot_survives_depth_four :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 4
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTAUpperRoot ∧ finiteFTAUpperRoot <= Z.hi ∧
      Z.width = 1 / 8 ∧ Z.height = 1 / 8 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTAUpperRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_upper_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 4 : Nat) : Rat) := hsize.1
      _ = 1 / 8 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 4 : Nat) : Rat) := hsize.2
      _ = 1 / 8 := by native_decide

theorem finiteFTALowerRoot_survives_depth_four :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 4
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTALowerRoot ∧ finiteFTALowerRoot <= Z.hi ∧
      Z.width = 1 / 8 ∧ Z.height = 1 / 8 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTALowerRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_lower_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 4 : Nat) : Rat) := hsize.1
      _ = 1 / 8 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 4 : Nat) : Rat) := hsize.2
      _ = 1 / 8 := by native_decide

theorem finiteFTAUpperRoot_survives_depth_five :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 5
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTAUpperRoot ∧ finiteFTAUpperRoot <= Z.hi ∧
      Z.width = 1 / 16 ∧ Z.height = 1 / 16 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTAUpperRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_upper_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 5 : Nat) : Rat) := hsize.1
      _ = 1 / 16 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 5 : Nat) : Rat) := hsize.2
      _ = 1 / 16 := by native_decide

theorem finiteFTALowerRoot_survives_depth_five :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 5
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTALowerRoot ∧ finiteFTALowerRoot <= Z.hi ∧
      Z.width = 1 / 16 ∧ Z.height = 1 / 16 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTALowerRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_lower_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 5 : Nat) : Rat) := hsize.1
      _ = 1 / 16 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 5 : Nat) : Rat) := hsize.2
      _ = 1 / 16 := by native_decide

theorem finiteFTAUpperRoot_survives_depth_six :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 6
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTAUpperRoot ∧ finiteFTAUpperRoot <= Z.hi ∧
      Z.width = 1 / 32 ∧ Z.height = 1 / 32 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTAUpperRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_upper_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 6 : Nat) : Rat) := hsize.1
      _ = 1 / 32 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 6 : Nat) : Rat) := hsize.2
      _ = 1 / 32 := by native_decide

theorem finiteFTALowerRoot_survives_depth_six :
    ∃ Z, Z ∈
        FiniteFTASubdivision.survivingSubdivide finiteFTAQuadratic 6
          finiteFTARootSearchDomain ∧
      Z.lo <= finiteFTALowerRoot ∧ finiteFTALowerRoot <= Z.hi ∧
      Z.width = 1 / 32 ∧ Z.height = 1 / 32 := by
  obtain ⟨Z, hZ, hZlo, hZhi⟩ :=
    FiniteFTASubdivision.root_mem_survivingSubdivide
      finiteFTARootSearchDomain_ordered (z := finiteFTALowerRoot)
      (by native_decide) (by native_decide)
      finiteFTAQuadratic_lower_root
  have hsize := FiniteFTASubdivision.survivingSubdivide_width_height_exact
    finiteFTARootSearchDomain_ordered hZ
  refine ⟨Z, hZ, hZlo, hZhi, ?_⟩
  constructor
  · calc
      Z.width = finiteFTARootSearchDomain.width / ((2 ^ 6 : Nat) : Rat) := hsize.1
      _ = 1 / 32 := by native_decide
  · calc
      Z.height = finiteFTARootSearchDomain.height / ((2 ^ 6 : Nat) : Rat) := hsize.2
      _ = 1 / 32 := by native_decide

end ComputableAnalysis
