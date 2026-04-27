import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Module Submodule

theorem classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : 2 ^ n < volume s) :
    ∃ x ≠ 0, (x ∈ s) ∧ (∀ i : Fin n, (∃ (m : ℤ), m = x i)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have : Countable (span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (span ℤ (Set.range b)))
  have fund : IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain' b volume
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [(ZSpan.fundamentalDomain_ae_parallelepiped b volume).measure_eq]
    exact (EuclideanSpace.basisFun _ _).volume_parallelepiped
  have hmeas : volume (ZSpan.fundamentalDomain b) *
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) < volume s := by
    simpa [hF, finrank_euclideanSpace_fin] using h
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hmeas
  refine ⟨x, fun h0 => hx_ne (Subtype.ext h0), hx_mem, fun i => ?_⟩
  obtain ⟨m, hm⟩ := (b.mem_span_iff_repr_mem ℤ x.1).mp x.2 i
  exact ⟨m, by simpa using hm⟩
