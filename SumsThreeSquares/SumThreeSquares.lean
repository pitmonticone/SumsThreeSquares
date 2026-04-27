import Mathlib
import SumsThreeSquares.MinkowskiConvex

open scoped BigOperators Real Int Nat Classical Pointwise
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
A number is the sum of three squares if it can be written as a^2 + b^2 + c^2.
-/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-- If the `p`-adic valuation of `n` is odd, then `p ∣ n` (since `padicValInt p n = 0`
when `p ∤ n`, and `0` is not odd). -/
private lemma dvd_of_odd_padicValInt {p : ℕ} {n : ℤ}
    (h : Odd (padicValInt p n)) : (p : ℤ) ∣ n := by
  by_contra hpn
  rw [padicValInt.eq_zero_of_not_dvd hpn] at h
  exact absurd h (by decide)

/-- If `p` is prime and `p ∣ k`, then `jacobiSym k p ≠ 1` (it is in fact `0`). -/
private lemma not_jacobiSym_eq_one_of_dvd {p : ℕ} (hp : Nat.Prime p) {k : ℤ} (hpk : (p : ℤ) ∣ k) :
    jacobiSym k p ≠ 1 := by
  rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd hpk, jacobiSym.zero_left hp.one_lt]
  decide

/-
There exists a prime `q` with `q ≡ 1 (mod 4)` and `(-2q/p) = 1` for all prime factors `p` of `m`.
-/

/-- For any natural `a` and any odd natural `p`, some shift `a + k * p` is `≡ 1 (mod 4)`.
(Since `gcd(p, 4) = 1`, multiplication by `p` is a permutation on `ZMod 4`.) -/
private lemma exists_shift_mod4_eq_one (a : ℕ) {p : ℕ} (hp_odd : Odd p) :
    ∃ k : ℕ, (a + k * p) % 4 = 1 := by
  have hp2 : p ^ 2 % 4 = 1 := by
    have : (p : ℤ) ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd (by exact_mod_cast hp_odd)
    exact_mod_cast this
  have heq : a + (3 * a + 1) * p * p = a + (3 * a + 1) * p ^ 2 := by ring
  exact ⟨(3 * a + 1) * p, by grind [Nat.add_mod, Nat.mul_mod]⟩

/-- For an odd prime `p`, there is a natural `a` coprime to `p` with `-2 * a` a quadratic
residue modulo `p`. Uses that `-2` is a unit in `(ZMod p)ˣ`, so the image of `-2 * _` covers
every residue class — pick any QR (e.g. 1) as preimage. -/
private lemma exists_coprime_neg_two_mul_qr_mod_odd_prime (p : ℕ) (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2) :
    ∃ a : ℕ, jacobiSym (-2 * a) p = 1 ∧ a % p ≠ 0 := by
  have h_gcd : Int.gcd (-2 : ℤ) p = 1 :=
    Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr fun h => hp_ne_two <|
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hy : (-2 : ℤ) * (-Int.gcdA 2 p) ≡ 1 [ZMOD p] := by
    have := Int.gcd_eq_gcd_ab 2 p
    norm_num +zetaDelta at h_gcd
    exact Int.modEq_iff_dvd.mpr ⟨Int.gcdB 2 p, by grind⟩
  obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, -2 * a_p ≡ (1 : ℤ) [ZMOD p] :=
    ⟨Int.toNat (-Int.gcdA 2 p % p), by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.mpr hp.ne_zero)]
      simpa [← ZMod.intCast_eq_intCast_iff, mul_assoc] using hy⟩
  refine ⟨a_p, ?_, ?_⟩
  · rw [jacobiSym.mod_left, ha_p, ← jacobiSym.mod_left]
    norm_num [jacobiSym]
  · intro h
    have := Fact.mk hp
    simp_all +decide [← ZMod.intCast_eq_intCast_iff, ← Nat.dvd_iff_mod_eq_zero,
      ← ZMod.natCast_eq_zero_iff]

/-- For an odd prime `p`, there is a natural `a ≡ 1 (mod 4)` coprime to `p` with `-2 * a`
a quadratic residue modulo `p`. Combines `exists_coprime_neg_two_mul_qr_mod_odd_prime` with
a shift by a multiple of `p` to fix the residue modulo 4. -/
private lemma exists_residue_neg_two_qr_mod_odd_prime (p : ℕ) (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2) :
    ∃ a : ℕ, jacobiSym (-2 * a) p = 1 ∧ a % p ≠ 0 ∧ a % 4 = 1 := by
  obtain ⟨a_p, ha_p_jac, ha_p_nd⟩ := exists_coprime_neg_two_mul_qr_mod_odd_prime p hp hp_ne_two
  obtain ⟨k, hk⟩ := exists_shift_mod4_eq_one a_p (hp.odd_of_ne_two hp_ne_two)
  refine ⟨a_p + k * p, ?_, ?_, hk⟩
  · have hrw : -2 * ((a_p + k * p : ℕ) : ℤ) = -2 * (a_p : ℤ) - (p : ℤ) * (2 * k) := by
      push_cast; ring
    rw [jacobiSym.mod_left, hrw, Int.sub_mul_emod_self_left, ← jacobiSym.mod_left]
    exact_mod_cast ha_p_jac
  · simp_all [Nat.add_mod, Nat.mul_mod]

/-- Chinese Remainder Theorem over the prime factors of an odd natural number `m`,
simultaneously achieving `≡ 1 (mod 4)`. Given per-prime residue data `a p`, we can find
a single `c` satisfying all the congruences `c ≡ a p (mod p)` for `p ∈ primeFactors m`
together with `c ≡ 1 (mod 4)`. -/
private lemma exists_crt_primeFactors_and_mod4 {m : ℕ} (hm_odd : Odd m) (a : ℕ → ℕ) :
    ∃ c : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → c ≡ a p [MOD p]) ∧ c ≡ 1 [MOD 4] := by
  have h_crt_exists : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p ∧ p ∣ m) →
      ∃ c : ℕ, (∀ p ∈ S, c ≡ a p [MOD p]) ∧ c ≡ 1 [MOD 4] := by
    intro S hS
    induction' S using Finset.induction with p S hpS ih
    · aesop
    obtain ⟨c, hc₁, hc₂⟩ := ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨x, hx⟩ : ∃ x : ℕ, x ≡ c [MOD 4 * Finset.prod S id] ∧ x ≡ a p [MOD p] := by
      obtain ⟨hp_prime, hp_dvd⟩ := hS p (Finset.mem_insert_self _ _)
      have hp_odd : Odd p := hp_prime.eq_two_or_odd'.resolve_left fun h => by
        rw [h] at hp_dvd; have := Nat.odd_iff.mp hm_odd; omega
      have h_cop : Nat.gcd (4 * Finset.prod S id) p = 1 :=
        Nat.Coprime.mul_left (Nat.Coprime.pow_left 2 hp_odd.coprime_two_left)
          (Nat.Coprime.prod_left fun q hq => Nat.coprime_comm.mp <|
            hp_prime.coprime_iff_not_dvd.mpr fun h => hpS <|
              ((Nat.prime_dvd_prime_iff_eq hp_prime
                (hS q (Finset.mem_insert_of_mem hq)).1).mp h) ▸ hq)
      exact ⟨_, (Nat.chineseRemainder h_cop c (a p)).2⟩
    refine ⟨x, ?_, (hx.1.of_dvd (dvd_mul_right _ _)).trans hc₂⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hx.2
    · exact (hx.1.of_dvd (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) _)).trans (hc₁ q hq)
  specialize @h_crt_exists (Nat.primeFactors m)
  aesop

/-- Dirichlet's theorem, packaged as an existence statement: for `a : ℕ` coprime to `N > 0`,
there is a prime `q > N` in the same residue class as `a` modulo `N`. -/
private lemma exists_prime_gt_eq_mod {a N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime a N) :
    ∃ q : ℕ, Nat.Prime q ∧ q % N = a % N ∧ N < q := by
  have : NeZero N := ⟨hN.ne'⟩
  have h_dir : Set.Infinite {q : ℕ | Nat.Prime q ∧ q % N = a % N} := by
    convert Nat.infinite_setOf_prime_and_eq_mod (q := N) (a := (a : ZMod N))
      ((ZMod.isUnit_iff_coprime a N).mpr hcop) using 1
    norm_num [← ZMod.natCast_eq_natCast_iff']
  obtain ⟨q, ⟨hq_prime, hq_mod⟩, hq_gt⟩ := h_dir.exists_gt N
  exact ⟨q, hq_prime, hq_mod, hq_gt⟩

lemma exists_prime_aux (m : ℕ) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have ha_p : ∀ p : ℕ, p ∣ m → Nat.Prime p → ∃ a_p : ℕ,
      jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 ∧ a_p % 4 = 1 := fun p hp hp_prime =>
    exists_residue_neg_two_qr_mod_odd_prime p hp_prime fun h => by
      subst h; have : 2 ∣ m := hp; omega
  choose! a ha using ha_p
  obtain ⟨a_crt, ha_crt_p, ha_crt_4⟩ := exists_crt_primeFactors_and_mod4 hm_odd a
  have ha_crt_cop : Nat.Coprime a_crt (4 * m) := by
    refine Nat.Coprime.mul_right (ha_crt_4.gcd_eq.trans (by norm_num)) ?_
    refine Nat.coprime_of_dvd' fun k hk hk₁ hk₂ => ?_
    grind [Nat.ModEq, Nat.dvd_iff_mod_eq_zero]
  obtain ⟨q, hq_prime, hq_mod, -⟩ := exists_prime_gt_eq_mod (by omega : 0 < 4 * m) ha_crt_cop
  refine ⟨q, hq_prime, ?_, fun p hp hp_prime => ?_⟩
  · rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 4 m), hq_mod,
        Nat.mod_mod_of_dvd _ (dvd_mul_right 4 m)]
    exact ha_crt_4
  · have h_qap : (q : ℤ) ≡ a p [ZMOD p] :=
      (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hp 4))
        (Int.natCast_modEq_iff.mpr hq_mod)).trans
        (Int.natCast_modEq_iff.mpr (ha_crt_p p hp hp_prime))
    rw [jacobiSym.mod_left (-2 * (q : ℤ)), (h_qap.mul_left (-2)), ← jacobiSym.mod_left]
    grind

/-
If `m ≡ 3 (mod 8)` is squarefree, `q ≡ 1 (mod 4)` is prime, and `(-2q/p) = 1` for all `p | m`,
then `(-m/q) = 1`.
-/
lemma exists_odd_sq_mod_prime_of_jacobi_eq_one (m q : ℕ) (hq_prime : Nat.Prime q)
    (hq_mod : q % 4 = 1) (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b : ℤ, b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b % 2 = 1 := by
  have := Fact.mk hq_prime
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one h_jacobi
  have hb₀ : (x.val : ℤ) ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  by_cases hb₀_odd : (x.val : ℤ) % 2 = 1
  · exact ⟨x.val, hb₀, hb₀_odd⟩
  · refine ⟨x.val + q, (Int.add_modEq_right.pow 2).trans hb₀, ?_⟩
    have hq_odd : (q : ℤ) % 2 = 1 := mod_cast hq_prime.eq_two_or_odd.resolve_left (by grind)
    grind

lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_mod : q % 4 = 1)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    jacobiSym (-m) q = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have h_qm : jacobiSym (-2 * q) m = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp hx
    have hp_prime := Nat.prime_of_mem_primeFactorsList hp
    have := Fact.mk hp_prime
    simpa [jacobiSym, Nat.primeFactorsList_prime hp_prime] using
      h_jacobi p (Nat.dvd_of_mem_primeFactorsList hp) hp_prime
  have h_qm' : jacobiSym q m = jacobiSym (-2) m := by
    grind [jacobiSym.mul_left, Int.mul_eq_one_iff_eq_one_or_neg_one]
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hq_odd, ZMod.χ₄_nat_one_mod_four hq_mod, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hm_odd hq_mod, h_qm',
      jacobiSym.mod_right _ hm_odd]
  norm_num [hm_mod]

/-
There exist integers $b$ and $h$ such that $b$ is odd and $b^2 - 4qh = -m$.
-/
lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b % 2 = 1 ∧ b^2 - 4 * q * h = -m := by
  obtain ⟨b, hb_mod_q, hb_odd⟩ :=
    exists_odd_sq_mod_prime_of_jacobi_eq_one m q hq_prime hq_mod h_jacobi
  have h_mod4 : b ^ 2 ≡ -↑m [ZMOD 4] := by
    grind [Int.ModEq, Int.sq_mod_four_eq_one_of_odd]
  have h_cop : ((4 : ℤ).natAbs).Coprime ((q : ℤ).natAbs) :=
    (hq_prime.coprime_iff_not_dvd.mpr fun h => by
      have := Nat.le_of_dvd (by decide) h; interval_cases q <;> trivial).symm
  have hb_mod : b ^ 2 ≡ -↑m [ZMOD (4 * ↑q : ℤ)] :=
    (Int.modEq_and_modEq_iff_modEq_mul h_cop).mp ⟨h_mod4, hb_mod_q⟩
  exact ⟨b, (b^2 - -m) / (4 * q), hb_odd,
    by have := Int.ediv_mul_cancel hb_mod.symm.dvd; grind⟩

/-
There exists an integer $t$ such that $2q t^2 \equiv -1 \pmod m$.
-/
/-- Per-prime existence: for a prime `p` with `2q` coprime to `p` and `(-2q/p) = 1`, there is
an integer `t_p` with `2q·t_p² ≡ -1 (mod p)`. The witness is `s · (2q)⁻¹` where `s² ≡ -2q`. -/
private lemma exists_t_local_of_jacobi (p q : ℕ) (hp : Nat.Prime p)
    (hp_cop : Nat.Coprime (2 * q) p) (hjac : jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, 2 * q * t ^ 2 ≡ -1 [ZMOD p] := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one hjac
  have hs : (x.val : ℤ) ^ 2 ≡ -2 * q [ZMOD p] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  obtain ⟨inv_2q, hinv_2q⟩ : ∃ inv_2q : ℤ, (2 * q : ℤ) * inv_2q ≡ 1 [ZMOD p] :=
    Int.mod_coprime hp_cop
  refine ⟨x.val * inv_2q, ?_⟩
  convert hs.mul_left (2 * q * inv_2q ^ 2) |>.trans ?_ using 1 <;> ring_nf
  convert (hinv_2q.pow 2).neg using 1
  ring

/-- If `m` is squarefree and an integer congruence `x ≡ y (mod p)` holds for every prime
factor `p` of `m`, then the congruence lifts to `x ≡ y (mod m)`. -/
private lemma int_modEq_of_forall_modEq_primeFactors_squarefree {m : ℕ} (hm : Squarefree m)
    {x y : ℤ} (h : ∀ p ∈ m.primeFactors, x ≡ y [ZMOD (p : ℤ)]) : x ≡ y [ZMOD m] := by
  have h_prod : (m : ℤ) = ∏ p ∈ m.primeFactors, (p : ℤ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm]
  rw [Int.modEq_iff_dvd, h_prod]
  refine Finset.prod_dvd_of_coprime (fun p hp q hq hpq => ?_)
    (fun p hp => Int.modEq_iff_dvd.mp (h p hp))
  have := Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)
  aesop

/-- Integer CRT over the prime factors of a squarefree number: given per-prime residue data,
produce a single integer matching all the congruences simultaneously. -/
private lemma exists_int_crt_primeFactors_squarefree {m : ℕ} (t : ℕ → ℤ) :
    ∃ x : ℤ, ∀ p ∈ m.primeFactors, x ≡ t p [ZMOD (p : ℤ)] := by
  let b : ℕ → ℕ := fun p => ((t p).emod p).toNat
  have h_ne_zero : ∀ p ∈ m.primeFactors, p ≠ 0 :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have h_pairwise : Set.Pairwise (m.primeFactors : Set ℕ) (fun p q => Nat.Coprime p q) :=
    fun p hp q hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset b id m.primeFactors h_ne_zero h_pairwise
  refine ⟨(c : ℤ), fun p hp => ?_⟩
  have h_b : (b p : ℤ) = (t p) % p :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast h_ne_zero p hp))
  have h1 : (c : ℤ) ≡ (b p : ℤ) [ZMOD (p : ℤ)] := by exact_mod_cast hc p hp
  exact h1.trans (by rw [Int.ModEq, h_b, Int.emod_emod_of_dvd _ dvd_rfl])

lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, (2 * q : ℤ) * t^2 ≡ -1 [ZMOD m] := by
  have h_tp : ∀ p ∈ Nat.primeFactors m, ∃ t_p : ℤ, 2 * q * t_p ^ 2 ≡ -1 [ZMOD (p : ℤ)] := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    refine exists_t_local_of_jacobi p q hp_prime (Nat.Coprime.mul_left ?_ ?_)
      (h_jacobi p hpm hp_prime)
    · exact Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p => by
        have : 2 ∣ m := dvd_trans h2p hpm; omega
    · rw [Nat.coprime_primes hq_prime hp_prime]
      rintro rfl
      exact not_jacobiSym_eq_one_of_dvd hq_prime (by simp) (h_jacobi q hpm hq_prime)
  choose! t ht using h_tp
  obtain ⟨x, hx⟩ := exists_int_crt_primeFactors_squarefree (m := m) t
  refine ⟨x, int_modEq_of_forall_modEq_primeFactors_squarefree hm_sq fun p hp => ?_⟩
  exact (((hx p hp).pow 2).mul_left _).trans (ht p hp)

noncomputable def linear_map_M (m q : ℕ) (t b : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (!![
    2 * t * q, t * b, m;
    Real.sqrt (2 * q), b / Real.sqrt (2 * q), 0;
    0, Real.sqrt m / Real.sqrt (2 * q), 0])

lemma det_linear_map_M (m q : ℕ) (t b : ℤ) (_hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M m q t b) = m * Real.sqrt m := by
  unfold linear_map_M
  simp +decide [Matrix.det_fin_three]
  rw [mul_assoc, mul_div_cancel₀ _ (by positivity)]

noncomputable abbrev linear_map_M_euclidean (m q : ℕ) (t b : ℤ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap ∘ₗ
    (linear_map_M m q t b) ∘ₗ (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap

lemma det_linear_map_M_euclidean (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M_euclidean m q t b) = m * Real.sqrt m := by
  have hrw : linear_map_M_euclidean m q t b =
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv :
        (Fin 3 → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).toLinearMap ∘ₗ (linear_map_M m q t b) ∘ₗ
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv.symm).toLinearMap := rfl
  rw [hrw, LinearMap.det_conj]
  exact det_linear_map_M m q t b hm hq

/-- Component formulas for the linear map `linear_map_M_euclidean`. -/
private lemma linear_map_M_euclidean_apply (m q : ℕ) (t b : ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
    (linear_map_M_euclidean m q t b x) 0 = 2 * t * q * x 0 + t * b * x 1 + m * x 2 ∧
    (linear_map_M_euclidean m q t b x) 1 =
      Real.sqrt (2 * q) * x 0 + b / Real.sqrt (2 * q) * x 1 ∧
    (linear_map_M_euclidean m q t b x) 2 = Real.sqrt m / Real.sqrt (2 * q) * x 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [linear_map_M_euclidean, linear_map_M, Matrix.toLin'_apply, Matrix.vecHead,
      Matrix.vecTail]; try ring)

lemma quad_form_decomposition (m q : ℕ) (b h x y : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 =
      2 * ((q : ℝ) * x ^ 2 + (b : ℝ) * x * y + (h : ℝ) * y ^ 2) := by
  have hb2 : (b : ℝ) ^ 2 = 4 * q * h - m := by
    have : (b : ℤ) ^ 2 = 4 * q * h - m := by grind
    exact_mod_cast this
  field_simp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * q),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), hb2]

/-- Minkowski volume certificate: the preimage under `linear_map_M_euclidean` of the ball
of radius `√(2m)` has volume strictly greater than `2^3 = 8`. -/
private lemma vol_preimage_ball_gt_eight (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    (2 : ENNReal) ^ 3 < MeasureTheory.volume
      ((linear_map_M_euclidean m q t b) ⁻¹'
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
  have hdet_ne : LinearMap.det (linear_map_M_euclidean m q t b) ≠ 0 := by
    rw [det_linear_map_M_euclidean m q t b hm hq]; positivity
  have h8 : ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8 := by norm_num
  have hrt : (Real.sqrt (2 * m)) ^ 3 = 2 * Real.sqrt 2 * ((m : ℝ) * Real.sqrt m) := by
    rw [pow_succ, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m),
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet_ne,
      det_linear_map_M_euclidean m q t b hm hq, EuclideanSpace.volume_ball_fin_three,
      abs_inv, abs_of_nonneg (by positivity),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), h8,
      ENNReal.ofReal_lt_ofReal_iff (by positivity), hrt]
  field_simp
  nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
    (by positivity : 0 < (m : ℝ) * Real.sqrt m)]

private lemma exists_lattice_xyz_lt_two_m (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    let R := (2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z
    let S := Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y
    let T := Real.sqrt m / Real.sqrt (2 * q) * y
    R^2 + S^2 + T^2 < 2 * m := by
  obtain ⟨x, hx0, hxs, h⟩ :=
    classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (fun x hx => by
        simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_neg, norm_neg] at *
        exact hx)
      (Convex.linear_preimage (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) _)
      (vol_preimage_ball_gt_eight m q t b hm hq)
  obtain ⟨R, hr⟩ := h 0
  obtain ⟨S, hs⟩ := h 1
  obtain ⟨T, ht⟩ := h 2
  refine ⟨R, S, T, ?_, ?_⟩
  · contrapose! hx0; ext i; fin_cases i <;> aesop
  · have hxs' : ‖linear_map_M_euclidean m q t b x‖ < Real.sqrt (2 * m) := by simpa using hxs
    have h_norm_sq : (‖linear_map_M_euclidean m q t b x‖ ^ 2 : ℝ) < 2 * m := by
      nlinarith [norm_nonneg (linear_map_M_euclidean m q t b x),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m)]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at h_norm_sq
    have h_expand := linear_map_M_euclidean_apply m q t b x
    rw [h_expand.1, h_expand.2.1, h_expand.2.2] at h_norm_sq
    convert h_norm_sq using 1
    push_cast [hr, hs, ht]
    ring

private lemma rst_modEq_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : t^2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) ≡ 0 [ZMOD m] := by
  obtain ⟨c, hc⟩ : (m : ℤ) ∣ t ^ 2 * 2 * q + 1 := by
    simpa [neg_sub] using (Int.modEq_iff_dvd.mp hqt).neg_right
  rw [Int.modEq_zero_iff_dvd]
  refine ⟨c * (2 * q * x ^ 2 + 2 * b * x * y + 2 * h * y ^ 2) +
    (4 * t * q * x * z + 2 * t * b * y * z + m * z ^ 2 - t ^ 2 * y ^ 2), ?_⟩
  linear_combination (2 * q * x ^ 2 + 2 * b * x * y + 2 * h * y ^ 2) * hc + t ^ 2 * y ^ 2 * hbqm

/-- The integer binary quadratic form `q·x² + b·x·y + h·y²` is nonnegative when its
discriminant is `-m < 0` (i.e. negative definite `-Δ`) and `q > 0`. -/
private lemma quadform_nonneg {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (x y : ℤ) :
    0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := by
  nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y), sq_nonneg (y : ℤ), hbqm,
    Int.natCast_nonneg m]

/-- The binary form `q·x² + b·x·y + h·y²` with `q > 0` and discriminant `-m < 0` has only the
trivial zero: `qf = 0 ↔ x = y = 0`. (Reverse direction is trivial; stated as `x = 0 ∧ y = 0`.) -/
private lemma quadform_eq_zero_imp_xy_zero {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) {x y : ℤ}
    (h_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  by_cases hy : y = 0
  · exact ⟨by subst hy; nlinarith [sq_nonneg x, hq, h_zero], hy⟩
  · refine absurd h_zero ?_
    nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y), mul_self_pos.mpr hy, hbqm]

/-- A nonnegative integer `n ≡ 0 (mod m)` with `n < 2m` is either `0` or `m`. -/
private lemma eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul {m : ℤ} (hm : 0 < m)
    {n : ℤ} (h_nn : 0 ≤ n) (h_mod : n ≡ 0 [ZMOD m]) (h_lt : n < 2 * m) :
    n = 0 ∨ n = m := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h_mod
  have hk0 : 0 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  interval_cases k <;> grind

/-- The discriminant `b² - 4qh` of an integer binary quadratic form cannot equal `-1`:
squares mod 4 are in `{0, 1}` but `-1 ≡ 3 (mod 4)`. -/
private lemma discriminant_ne_neg_one (q : ℕ) (b h : ℤ) : b ^ 2 - 4 * (q : ℤ) * h ≠ -1 := by
  rcases Int.even_or_odd b with ⟨k, rfl⟩ | hb <;> grind [Int.sq_mod_four_eq_one_of_odd]

lemma exists_Rv_from_Minkowski (m q : ℕ) (t b h : ℤ) (hm : 0 < m) (hq : 0 < q)
    (hqt : t ^ 2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    ∃ (x y : ℤ) (R : ℤ) (v : ℕ),
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨x, y, z, hne, hlt⟩ :
      ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧
      (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
        (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
        (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 < 2 * m := by
    simpa using exists_lattice_xyz_lt_two_m m q t b hm hq
  have hqf_nn : 0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := quadform_nonneg hq hbqm x y
  -- `R² + 2·qf` is nonneg, `< 2m`, and `≡ 0 (mod m)`, hence `∈ {0, m}`.
  have h_lt : (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
      2 * ((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2) < 2 * m := by
    have hqfd := quad_form_decomposition m q b h x y hq (by exact_mod_cast hbqm)
    have : ((2 * t * q * x + t * b * y + m * z : ℤ) : ℝ) ^ 2 +
        2 * (((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 : ℤ) : ℝ) < 2 * m := by push_cast; linarith
    exact_mod_cast this
  have h_cases := eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul
    (by exact_mod_cast hm : (0 : ℤ) < m) (by positivity)
    (rst_modEq_zero m q t b h x y z hqt hbqm) h_lt
  rcases h_cases with h_case1 | h_case2
  · have h_qf0 : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * t * q * x + t * b * y + m * z : ℤ)]
    obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm h_qf0
    obtain rfl : z = 0 :=
      (mul_eq_zero.mp (by nlinarith : (m : ℤ) * z = 0)).resolve_left (by exact_mod_cast hm.ne')
    exact absurd rfl hne
  · refine ⟨x, y, 2 * t * q * x + t * b * y + m * z,
      Int.toNat (q * x ^ 2 + b * x * y + h * y ^ 2), ?_, ?_, ?_⟩ <;> norm_num
    · exact hqf_nn
    · grind
    · contrapose! hne
      have hqf_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
        nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y)]
      obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm hqf_zero
      simp_all +decide
      rcases m with _ | _ | m <;> norm_num at *
      · exact absurd hbqm (discriminant_ne_neg_one q b h)
      · have hz : z ^ 2 * (m + 1 + 1) = 1 := by nlinarith
        nlinarith [hz]

/-- There exist q, b, h, t, x, y, z yielding R² + 2v = m with v > 0 -/
lemma exists_R_v_of_mod8_eq3 (m : ℕ) (hm : Squarefree m) (hm_pos : 0 < m) (hmod : m % 8 = 3) :
    ∃ (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ),
      Nat.Prime q ∧ q % 4 = 1 ∧
      (∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) ∧
      b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ) ∧
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨q, hq_prime, hq_mod, hjac⟩ := exists_prime_aux m hmod
  obtain ⟨b, h, _, hbqm⟩ :=
    exists_b_h m q hmod hq_prime hq_mod (jacobi_neg_m_q m q hmod hq_mod hjac)
  obtain ⟨t, hqt⟩ := exists_t m q hm hmod hq_prime hjac
  have hqt' : t ^ 2 * 2 * q ≡ -1 [ZMOD m] := by simpa [mul_assoc, mul_comm, mul_left_comm] using hqt
  obtain ⟨x, y, R, v, hv_def, hRv, hv_pos⟩ :=
    exists_Rv_from_Minkowski m q t b h hm_pos (hq_prime.pos) hqt' hbqm
  exact ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩

lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2) (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  have := Fact.mk hp
  rw [jacobiSym]
  norm_num [Nat.primeFactorsList_prime hp]
  simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd, legendreSym.eq_one_iff]
  use a / b'
  grind

lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : Odd (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  induction' n : Int.natAbs a + Int.natAbs b' using Nat.strong_induction_on with n ih
    generalizing a b'
  by_cases h_div_b' : (p : ℤ) ∣ b'
  · obtain ⟨k, hk⟩ := h_div_b'
    obtain ⟨a', ha'⟩ : ∃ a', a = p * a' :=
      Int.Prime.dvd_pow' hp <| by
        simpa [hk, ← ZMod.intCast_zmod_eq_zero_iff_dvd] using dvd_of_odd_padicValInt h_odd_val
    contrapose! ih
    refine ⟨a'.natAbs + k.natAbs, ?_, a', k, ?_, rfl, ih⟩
    · rcases eq_or_ne a' 0 with ha0 | ha0 <;> rcases eq_or_ne k 0 with hk0 | hk0 <;>
        simp_all +decide [Int.natAbs_mul]
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hk0) hp.one_lt
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr ha0) hp.one_lt
      · nlinarith [hp.two_le, abs_pos.mpr ha0, abs_pos.mpr hk0]
    · simp_all +decide [padicValInt, parity_simps]
      have hfactor : (p * a') ^ 2 + d * (p * k) ^ 2 = p ^ 2 * (a' ^ 2 + d * k ^ 2) := by ring
      rw [hfactor, Int.natAbs_mul, Int.natAbs_pow] at h_odd_val
      have := Fact.mk hp
      rw [padicValNat.mul] at h_odd_val <;> simp_all +decide [parity_simps]
      · exact hp.ne_zero
      · intro H; simp_all +decide
  · exact jacobi_neg_d_of_dvd_sq_add p a d b' hp (dvd_of_odd_padicValInt h_odd_val)
      hp_not_dvd_d h_div_b'

/-- Completing-the-square for the binary form: `4·q·v = (2·q·x + b·y)² + m·y²` when
`v = q·x² + b·x·y + h·y²` and `b² - 4·q·h = -m`. -/
private lemma four_q_v_eq_sq_plus_m_y_sq {m : ℕ} {q : ℤ} {b h x y v : ℤ}
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -(m : ℤ)) :
    4 * q * v = (2 * q * x + b * y) ^ 2 + (m : ℤ) * y ^ 2 := by
  rw [hv]; linear_combination -hbqm * y ^ 2

/-- If `R² ≡ a (mod p)` with `p ∤ a` and `p` an odd prime, then `(a/p) = 1` (Jacobi/Legendre). -/
private lemma jacobiSym_eq_one_of_sq_modEq {p : ℕ} (hp : Nat.Prime p) {a R : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hRa : R ^ 2 ≡ a [ZMOD p]) :
    jacobiSym a p = 1 := by
  have := Fact.mk hp
  simp_all +decide [← ZMod.intCast_eq_intCast_iff, jacobiSym,
    Nat.primeFactorsList_prime hp]
  rw [legendreSym.eq_one_iff]
  · exact ⟨R, by simpa [sq] using hRa.symm⟩
  · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpa

/-- For an odd prime `p` coprime to `q` and dividing a nonzero integer `v`,
`padicValInt p (4qv) = padicValInt p v`. -/
private lemma padicValInt_four_q_v {p : ℕ} {q v : ℤ}
    (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hpq : ¬ (p : ℤ) ∣ q) (hpv : Odd (padicValInt p v)) :
    padicValInt p (4 * q * v) = padicValInt p v := by
  have := Fact.mk hp
  rw [padicValInt.mul, padicValInt.mul] <;> norm_num
  · refine ⟨Or.inr <| mod_cast fun h => hp_odd ?_, Or.inr <| Or.inr hpq⟩
    have := Nat.le_of_dvd (by decide) h
    interval_cases p <;> trivial
  all_goals aesop

lemma p_mod4_eq1_of_dvd_v_not_dvd_m (p : ℕ) (q : ℤ) (b h x y v R m : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -m)
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : Odd (padicValInt p v))
    (hpm : ¬ (p : ℤ) ∣ m) :
    p % 4 = 1 := by
  have hpv_dvd : (p : ℤ) ∣ v := dvd_of_odd_padicValInt hpv
  have h_diff : (m - R ^ 2 : ℤ) = 2 * v := by grind
  have h_jacobi_m : jacobiSym m p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp hpm (R := R)
      (Int.modEq_iff_dvd.mpr (by rw [h_diff]; exact hpv_dvd.mul_left 2))
  have h_jacobi_neg_m : jacobiSym (-m) p = 1 := by
    by_cases hpq : (p : ℤ) ∣ q
    · -- `p | q`: then `b² - 4qh = -m` gives `b² ≡ -m (mod p)`, so `(-m/p) = 1`.
      refine jacobiSym_eq_one_of_sq_modEq hp (by simpa using hpm) (R := b) ?_
      exact Int.modEq_iff_dvd.mpr ⟨-4 * h * hpq.choose,
        by linear_combination -hbqm - 4 * h * hpq.choose_spec⟩
    · have h_padic := padicValInt_four_q_v hp hp_odd hpq hpv
      apply jacobi_neg_d_of_odd_padicVal p (2 * q * x + b * y) m y hp hpm
      grind
  rw [jacobiSym.neg _ (hp.odd_of_ne_two hp_odd), h_jacobi_m, mul_one,
    ZMod.χ₄_nat_mod_four] at h_jacobi_neg_m
  have := Nat.mod_lt p zero_lt_four
  interval_cases p % 4 <;> trivial

/-- If `R² + 2v = m`, `p` is a prime dividing both `v` and `m`, then `p ∣ R`. -/
private lemma dvd_R_of_dvd_v_dvd_m {p : ℕ} (hp : Nat.Prime p) {R v : ℤ} {m : ℕ}
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) : (p : ℤ) ∣ R :=
  Int.Prime.dvd_pow' hp <| by
    rw [← Int.dvd_add_left (dvd_mul_of_dvd_right hpv _)]
    exact hRv.symm ▸ Int.natCast_dvd_natCast.mpr hpm

/-- Given `v = qx² + bxy + hy²`, `b² - 4qh = -m`, a prime `p ∣ v` and `p ∣ m`, then
`p ∣ (2qx + by)`. Uses the identity `4qv = (2qx + by)² + m·y²`. -/
private lemma dvd_two_q_x_add_b_y_of_dvd_v_dvd_m {p q : ℕ} {b h x y v : ℤ} {m : ℕ}
    (hp : Nat.Prime p) (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) : (p : ℤ) ∣ (2 * q * x + b * y) := by
  have h_sum : (p : ℤ) ∣ ((2 * q * x + b * y) ^ 2 + m * y ^ 2) := by
    rw [← four_q_v_eq_sq_plus_m_y_sq hv hbqm]
    exact hpv.mul_left (4 * q)
  exact Int.Prime.dvd_pow' hp <|
    (Int.dvd_add_left ((Int.natCast_dvd_natCast.mpr hpm).mul_right _)).mp h_sum

/-- The quadratic residue extraction: given the problem hypotheses with `p` a prime
dividing both `v` and `m` (and `m` squarefree), we have `y² ≡ 2q (mod p)`. -/
private lemma y_sq_modEq_two_mul_q {p q : ℕ} {b h x y : ℤ} {R v : ℤ} {m : ℕ}
    (hp : Nat.Prime p) (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) :
    y ^ 2 ≡ 2 * q [ZMOD p] := by
  have hp_R := dvd_R_of_dvd_v_dvd_m hp hRv hpv hpm
  have hp_2qx_by := dvd_two_q_x_add_b_y_of_dvd_v_dvd_m hp hv hbqm hpv hpm
  have h_div_p : (m / p : ℤ) * y ^ 2 ≡ (m / p : ℤ) * (2 * q) [ZMOD p] := by
    have h_div_p : (4 * q * v : ℤ) ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
      obtain ⟨k, hk⟩ := hpv
      simp_all +decide [Int.modEq_iff_dvd]
      obtain ⟨a, ha⟩ := hp_R
      obtain ⟨b', hb'⟩ := hp_2qx_by
      simp_all +decide [← eq_sub_iff_add_eq', ← mul_assoc]
      exact ⟨a ^ 2 * 2 * q, by nlinarith⟩
    have h_div_p : (4 * q * v : ℤ) ≡ (2 * q * x + b * y) ^ 2 + m * y ^ 2 [ZMOD p ^ 2] :=
      (four_q_v_eq_sq_plus_m_y_sq hv hbqm) ▸ .refl _
    have h_div_p : (m : ℤ) * y ^ 2 ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
      simp_all +decide [Int.ModEq]
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at *
      aesop
    rw [Int.modEq_iff_dvd] at *
    obtain ⟨k, hk⟩ := h_div_p
    use k
    have hpm' : (p : ℤ) ∣ m := mod_cast hpm
    nlinarith [hp.two_le, Int.ediv_mul_cancel hpm']
  have := Fact.mk hp
  simp_all +decide [← ZMod.intCast_eq_intCast_iff]
  cases h_div_p <;> simp_all +decide [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_cast at *
  simp_all +decide [Nat.squarefree_iff_prime_squarefree]

lemma p_mod4_of_dvd_v_dvd_m (p : ℕ) (q : ℕ) (b h x y : ℤ) (R v : ℤ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m)
    (hjac : jacobiSym (-2 * q) p = 1) :
    False := by
  have h_jacobi_2q_p : jacobiSym (2 * q) p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp
      (fun h2q => not_jacobiSym_eq_one_of_dvd hp (by simpa [neg_mul] using h2q.neg_right) hjac)
      (y_sq_modEq_two_mul_q hp hm_sq hv hbqm hRv hpv hpm)
  simp only [neg_mul] at hjac
  rw [jacobiSym.neg _ (hp.odd_of_ne_two (by omega)), ZMod.χ₄_nat_mod_four, hp3,
      h_jacobi_2q_p, mul_one] at hjac
  exact absurd hjac (by decide)

lemma even_padicVal_of_mod4_eq3 (p : ℕ) (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hm_sq : Squarefree m) (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → jacobiSym (-2 * ↑q) ↑p' = 1) :
    Even (padicValNat p (2 * v)) := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hEven : Even (padicValInt p v) := by
    by_contra h_even
    have h_odd : Odd (padicValInt p v) := Nat.not_even_iff_odd.mp h_even
    by_cases hpm : (p : ℕ) ∣ m
    · exact p_mod4_of_dvd_v_dvd_m p q b h x y R v m hp hp3 hm_sq hv_def hbqm hRv
        (dvd_of_odd_padicValInt h_odd) hpm (hjac p hpm hp)
    · have := p_mod4_eq1_of_dvd_v_not_dvd_m p q b h x y v R m hp hp2 hv_def hbqm hRv h_odd
        (by exact_mod_cast hpm)
      omega
  rw [padicValNat.mul (by omega) hv_pos.ne',
    padicValNat.eq_zero_of_not_dvd fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h), zero_add,
    ← padicValInt.of_nat]
  exact hEven

lemma two_v_sum_two_squares (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ) (hm_sq : Squarefree m)
    (hv_pos : 0 < v) (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) :
    ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  exact fun p hp hp3 => even_padicVal_of_mod4_eq3 p q b h x y R v m
    (Nat.prime_of_mem_primeFactors hp) hp3 hm_sq hv_pos hv_def hbqm hRv hjac

/-- The final theorem -/
theorem blueprint_case_mod8_eq3 (m : ℕ) (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hm_mod : m % 8 = 3) : IsSumOfThreeSquares m := by
  obtain ⟨q, b, h, x, y, R, v, _, _, hjac, hbqm, hv_def, hRv, hv_pos⟩ :=
    exists_R_v_of_mod8_eq3 m hm_sq hm_pos hm_mod
  have h2v := two_v_sum_two_squares q b h x y R v m hm_sq hv_pos hv_def hbqm hRv hjac
  obtain ⟨a, b, c, habc⟩ : ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by grind +qlia
  exact ⟨a.natAbs, b.natAbs, c.natAbs, by grind [Int.natCast_natAbs, sq_abs]⟩
end
