import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
--import SumsThreeSquares.volumehypercube

open MeasureTheory Module Submodule

variable {n : ℕ}
variable {s : Set (EuclideanSpace ℝ (Fin n))}

theorem classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : 2 ^ n < volume s) :
    ∃ x ≠ 0, (x ∈ s) ∧ (∀ i : Fin n, (∃ (m : ℤ), m = x i)) := by

  -- Set up the type E = ℝ^n
  let E := EuclideanSpace ℝ (Fin n)

  -- The integer lattice ℤ^n as an AddSubgroup of ℝ^n
  -- Define it as the set of points with integer coordinates
  let L : AddSubgroup E := {
    carrier := {x : E | ∀ i, ∃ m : ℤ, (m : ℝ) = x i}
    zero_mem' := by
      simp
      intro i
      use 0
      simp
      exact rfl
    add_mem' := by
      simp
      intro a b ha hb i
      obtain ⟨ma, hma⟩ := ha i
      obtain ⟨mb, hmb⟩ := hb i
      use ma + mb
      rw [@Pi.add_apply]
      simp [hma, hmb]
    neg_mem' := by
      intro a ha i
      obtain ⟨m, hm⟩ := ha i
      use -m
      rw [@Pi.neg_apply]
      rw [← hm]
      simp
  }

  -- The fundamental domain [0,1)^n
  let F : Set E := Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)

  -- L is countable
  haveI : Countable L := by
    -- L is equivalent to Fin n → ℤ which is countable
    let f : L → (Fin n → ℤ) := fun x => fun i => (x.property i).choose
    have hf_inj : Function.Injective f := by
      intro x y hxy
      ext1; ext i
      have hx := (x.property i).choose_spec
      have hy := (y.property i).choose_spec
      calc (x : E) i = (f x i : ℝ) := hx.symm
        _ = (f y i : ℝ) := by rw [congr_fun hxy i]
        _ = (y : E) i := hy
    exact hf_inj.countable

  -- L has discrete topology
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    -- Show {0} is open in the subspace topology
    -- We use the fact that the open ball of radius 1/2 around 0 intersects L only at 0
    let U := Metric.ball (0 : E) (1/2)
    have hU_open : IsOpen U := Metric.isOpen_ball
    have eq : ({(0 : L)} : Set L) = Subtype.val ⁻¹' U := by
      ext ⟨x, hx⟩
      simp [U, Metric.mem_ball, Set.mem_singleton_iff, dist_zero_right]
      constructor
      · intro h; subst h; norm_num
      · intro hdist
        ext i
        by_contra hne
        obtain ⟨m, hm⟩ := hx i
        have hm_ne : m ≠ 0 := by
          intro h0; simp [h0] at hm; exact hne hm.symm
        have : (1 : ℝ) ≤ |x i| := by
          calc (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm_ne
            _ = |x i| := by rw [← hm]
        have : (1 : ℝ) ≤ ‖x‖ := by

          rw [EuclideanSpace.norm_eq]
          apply Real.le_sqrt_of_sq_le
          grw [← Finset.single_le_sum (a := i)]
          · rw [sq_le_sq]
            simp
            exact this
          · intros
            positivity
          · simp
        linarith
    rw [eq]
    exact IsOpen.preimage continuous_subtype_val hU_open

  -- F is a fundamental domain for L
  have fund : IsAddFundamentalDomain L F volume := by
    apply IsAddFundamentalDomain.mk'
    · -- F is null measurable
      exact (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico).nullMeasurableSet
    · -- For each x, there exists a unique g ∈ L such that g +ᵥ x ∈ F
      intro x
      -- The unique element is g = -⌊x⌋ (negative floor of each coordinate)
      -- So that g + x = x - ⌊x⌋ ∈ [0, 1)
      let g : Fin n → ℤ := fun i => -⌊x i⌋
      have hg : (fun i => (g i : ℝ)) ∈ L := by
        intro i; use g i
      use ⟨fun i => (g i : ℝ), hg⟩
      constructor
      · -- Show g +ᵥ x ∈ F, i.e., -⌊x⌋ + x ∈ [0, 1)
        simp only [VAdd.vadd, HVAdd.hVAdd, F]
        intro i _
        show (g i : ℝ) + x i ∈ Set.Ico 0 1
        simp only [g]
        change ((-⌊x i⌋ : ℤ) : ℝ) + x i ∈ Set.Ico 0 1
        rw [Int.cast_neg, neg_add_eq_sub, Set.mem_Ico]
        exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      · -- Show uniqueness
        intro ⟨y, hy⟩ hy_in_F
        ext1; ext i
        simp only [VAdd.vadd, HVAdd.hVAdd, F] at hy_in_F
        -- Extract that y has integer coordinates
        obtain ⟨m, hm⟩ := hy i
        -- y + x ∈ [0, 1)
        have h_in_F : y i + x i ∈ Set.Ico (0 : ℝ) 1 := hy_in_F i trivial
        -- Also -⌊x⌋ + x ∈ [0, 1)
        have h_floor : (-⌊x i⌋ : ℝ) + x i ∈ Set.Ico (0 : ℝ) 1 := by
          have := Int.fract_nonneg (x i)
          have h1 := Int.fract_lt_one (x i)
          rw [Int.fract] at this h1
          constructor
          · linarith
          · linarith
        -- Therefore m = -⌊x⌋
        rw [← hm] at h_in_F
        have : m = -⌊x i⌋ := by
          by_contra hne
          have h_in_F' := h_in_F
          rw [Set.mem_Ico] at h_in_F h_floor

          have := Int.lt_or_gt_of_ne hne
          cases this with
          | inl hlt =>-- If m < -⌊x⌋
              have : m + 1 ≤ -⌊x i⌋ := Int.lt_iff_add_one_le.mp hlt
              have hcast : (m : ℝ) + 1 ≤ (-⌊x i⌋ : ℝ) := by exact_mod_cast this
              linarith [h_in_F.2, h_floor.1]
          | inr hrt =>
              have : -⌊x i⌋ + 1 ≤ m := Int.lt_iff_add_one_le.mp hrt
              have hcast : (-⌊x i⌋ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast this
              linarith [h_in_F.1, h_floor.2]
        simp [g, ← hm, this]

  -- The measure of F is 1
  have hF : volume F = 1 := by
    have h_volume : MeasureTheory.volume (Set.pi Set.univ fun _ : Fin n => Set.Ico (0 : ℝ) 1) = 1 := by
      erw [ Real.volume_pi_Ico ] ; norm_num;
    convert h_volume using 1;
    convert ( EuclideanSpace.volume_preserving_measurableEquiv ( Fin n ) |> MeasureTheory.MeasurePreserving.measure_preimage ) _;
    · exact rfl;
    · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.univ_pi fun _ => measurableSet_Ico )

  -- The finite rank of ℝ^n is n
  have hrank : finrank ℝ E = n := by
    simp [E]

  -- Apply Minkowski's theorem
  have hmeas : volume F * 2 ^ finrank ℝ E < volume s := by
    rw [hF, hrank]
    simp only [one_mul]
    exact h

  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hmeas

  use (x : E)
  refine ⟨?_, hx_mem, ?_⟩
  · intro h0
    apply hx_ne
    ext1
    simp [h0]

  -- Show that x has integer coordinates
  intro i
  -- x is in the lattice L by definition
  exact x.property i

#min_imports
