import Mathlib
import SumsThreeSquares.MinkowskiConvex


open scoped BigOperators
open scoped Real Int
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
A number is the sum of three squares if it can be written as a^2 + b^2 + c^2.
-/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n


/-
There exists a prime $q$ such that $q \equiv 1 \pmod 4$ and $(-2q/p) = 1$ for all prime factors $p$ of $m$.
-/


/-- For any natural `a` and any odd natural `p`, some shift `a + k * p` is `≡ 1 (mod 4)`.
(Since `gcd(p, 4) = 1`, multiplication by `p` is a permutation on `ZMod 4`.) -/
private lemma exists_shift_mod4_eq_one (a : ℕ) {p : ℕ} (hp_odd : Odd p) :
    ∃ k : ℕ, (a + k * p) % 4 = 1 := by
  have hp_mod2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
  norm_num [Nat.add_mod, Nat.mul_mod]
  have := Nat.mod_lt a zero_lt_four
  have := Nat.mod_lt p zero_lt_four
  interval_cases _ : a % 4 <;> interval_cases _ : p % 4 <;> simp_all +decide
  all_goals simp_all +decide [← Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4)]
  exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨3, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨2, rfl⟩]

/-- For an odd prime `p`, there is a natural `a` coprime to `p` with `-2 * a` a quadratic
residue modulo `p`. Uses that `-2` is a unit in `(ZMod p)ˣ`, so the image of `-2 * _` covers
every residue class — pick any QR (e.g. 1) as preimage. -/
private lemma exists_coprime_neg_two_mul_qr_mod_odd_prime (p : ℕ) (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2) :
    ∃ a : ℕ, jacobiSym (-2 * a) p = 1 ∧ a % p ≠ 0 := by
  -- Pick the quadratic residue `1 (mod p)` and pull back through multiplication by `-2`.
  have h_inv : ∃ y : ℤ, -2 * y ≡ 1 [ZMOD p] := by
    have h_gcd : Int.gcd (-2 : ℤ) p = 1 :=
      Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr fun h => hp_ne_two <| by
        have := Nat.le_of_dvd (by decide) h; interval_cases p <;> trivial)
    norm_num +zetaDelta at *
    have := Int.gcd_eq_gcd_ab 2 p
    exact ⟨-Int.gcdA 2 p, Int.modEq_iff_dvd.mpr ⟨Int.gcdB 2 p, by linarith⟩⟩
  obtain ⟨y, hy⟩ := h_inv
  obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, -2 * a_p ≡ (1 : ℤ) [ZMOD p] :=
    ⟨Int.toNat (y % p), by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.mpr hp.ne_zero)]
      simpa [← ZMod.intCast_eq_intCast_iff, mul_assoc] using hy⟩
  refine ⟨a_p, ?_, ?_⟩
  · rw [jacobiSym.mod_left, ha_p, ← jacobiSym.mod_left]
    norm_num [jacobiSym]
  · intro h
    haveI := Fact.mk hp
    simp_all +decide [← ZMod.intCast_eq_intCast_iff]
    simp_all +decide [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]

/-- For an odd prime `p`, there is a natural `a ≡ 1 (mod 4)` coprime to `p` with `-2 * a`
a quadratic residue modulo `p`. Combines `exists_coprime_neg_two_mul_qr_mod_odd_prime` with
a shift by a multiple of `p` to fix the residue modulo 4. -/
private lemma exists_residue_neg_two_qr_mod_odd_prime (p : ℕ) (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2) :
    ∃ a : ℕ, jacobiSym (-2 * a) p = 1 ∧ a % p ≠ 0 ∧ a % 4 = 1 := by
  obtain ⟨a_p, ha_p_jac, ha_p_nd⟩ := exists_coprime_neg_two_mul_qr_mod_odd_prime p hp hp_ne_two
  have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
  obtain ⟨k, hk⟩ := exists_shift_mod4_eq_one a_p hp_odd
  refine ⟨a_p + k * p, ?_, ?_, hk⟩
  · have hring : (-(2 * ((a_p : ℤ) + k * p))) = -(2 * a_p) + (-(2 * k * p)) := by ring
    rw [show ((-2 : ℤ) * ((a_p + k * p : ℕ) : ℤ)) = -(2 * a_p) + (-(2 * k * p)) by push_cast; ring,
      jacobiSym.mod_left]
    simp_all only [Int.add_neg_mul_emod_self_right]
    rw [eq_comm, jacobiSym.mod_left] at *
    simp_all
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
    -- Combine the inductive solution with the new prime `p` using CRT over `4 * ∏ S`.
    obtain ⟨x, hx⟩ : ∃ x : ℕ, x ≡ c [MOD 4 * Finset.prod S id] ∧ x ≡ a p [MOD p] := by
      have h_cop : Nat.gcd (4 * Finset.prod S id) p = 1 := by
        refine Nat.Coprime.mul_left ?_ ?_
        · have := hS p (Finset.mem_insert_self _ _)
          rcases this with ⟨hp₁, hp₂⟩
          exact Nat.Coprime.pow_left 2 (Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by
            -- `p = 2` with `p ∣ m` would contradict `Odd m`.
            have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm_odd
            have : 2 ∣ m := dvd_trans h hp₂
            omega)
        · exact Nat.Coprime.prod_left fun q hq => Nat.coprime_comm.mp <|
            hS p (Finset.mem_insert_self _ _) |>.1.coprime_iff_not_dvd.mpr fun h => hpS <| by
              have := Nat.prime_dvd_prime_iff_eq (hS p (Finset.mem_insert_self _ _) |>.1)
                (hS q (Finset.mem_insert_of_mem hq) |>.1)
              aesop
      exact ⟨_, (Nat.chineseRemainder h_cop c (a p)).2⟩
    refine ⟨x, ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact hx.2
      · exact (hx.1.of_dvd (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) _)).trans
          (hc₁ q hq)
    · exact (hx.1.of_dvd (dvd_mul_right _ _)).trans hc₂
  specialize @h_crt_exists (Nat.primeFactors m)
  aesop

/-- Dirichlet's theorem, packaged as an existence statement: for `a : ℕ` coprime to `N > 0`,
there is a prime `q > N` in the same residue class as `a` modulo `N`. -/
private lemma exists_prime_gt_eq_mod {a N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime a N) :
    ∃ q : ℕ, Nat.Prime q ∧ q % N = a % N ∧ N < q := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h_dir : Set.Infinite {q : ℕ | Nat.Prime q ∧ q % N = a % N} := by
    have hinf := Nat.infinite_setOf_prime_and_eq_mod (q := N) (a := (a : ZMod N))
      ((ZMod.isUnit_iff_coprime a N).mpr hcop)
    convert hinf using 1
    norm_num [← ZMod.natCast_eq_natCast_iff']
  obtain ⟨q, hq_mem, hq_gt⟩ := h_dir.exists_gt N
  exact ⟨q, hq_mem.1, hq_mem.2, hq_gt⟩

lemma exists_prime_aux (m : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  -- Per-prime data: every prime factor `p` of `m` is odd, so apply the local lemma.
  have ha_p : ∀ p : ℕ, p ∣ m → Nat.Prime p → ∃ a_p : ℕ,
      jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 ∧ a_p % 4 = 1 := fun p hp hp_prime =>
    exists_residue_neg_two_qr_mod_odd_prime p hp_prime fun h => by
      subst h; have : 2 ∣ m := hp; omega
  choose! a ha using ha_p
  -- CRT over primeFactors m plus `≡ 1 (mod 4)`.
  obtain ⟨a_crt, ha_crt_p, ha_crt_4⟩ := exists_crt_primeFactors_and_mod4 hm_odd a
  -- The resulting `a_crt` is automatically coprime to `4 * m`.
  have ha_crt_cop : Nat.Coprime a_crt (4 * m) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact ha_crt_4.gcd_eq.trans (by norm_num)
    · refine Nat.coprime_of_dvd' fun k hk hk₁ hk₂ => ?_
      have h_ak_nd := (ha k hk₂ hk).2.1
      have := ha_crt_p k hk₂ hk
      simp_all +decide [Nat.ModEq, Nat.dvd_iff_mod_eq_zero]
  -- Dirichlet: a prime `q` in the class of `a_crt` mod `4m`.
  have h4m_pos : 0 < 4 * m := by omega
  obtain ⟨q, hq_prime, hq_mod, -⟩ := exists_prime_gt_eq_mod h4m_pos ha_crt_cop
  refine ⟨q, hq_prime, ?_, fun p hp hp_prime => ?_⟩
  · -- `q % 4 = 1` from `q ≡ a_crt (mod 4m)` and `a_crt ≡ 1 (mod 4)`.
    rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 4 m), hq_mod,
      Nat.mod_mod_of_dvd _ (dvd_mul_right 4 m)]
    exact ha_crt_4
  · -- Jacobi agreement: `q ≡ a_crt ≡ a p (mod p)`, so `(-2q/p) = (-2·a p /p) = 1`.
    have h_qa : (q : ℤ) ≡ a_crt [ZMOD p] :=
      Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hp 4))
        (Int.natCast_modEq_iff.mpr hq_mod)
    have h_ap : (a_crt : ℤ) ≡ a p [ZMOD p] := Int.natCast_modEq_iff.mpr (ha_crt_p p hp hp_prime)
    have h_chain : (-2 * (q : ℤ)) % p = (-2 * (a p : ℤ)) % p :=
      (h_qa.trans h_ap).mul_left _
    have heq : jacobiSym (-2 * (q : ℤ)) p = jacobiSym (-2 * (a p : ℤ)) p := by
      rw [jacobiSym.mod_left (-2 * (q : ℤ)), h_chain, ← jacobiSym.mod_left (-2 * (a p : ℤ))]
    rw [heq]
    exact (ha p hp hp_prime).1

/-
If $m \equiv 3 \pmod 8$ is squarefree, $q \equiv 1 \pmod 4$ is prime, and $(-2q/p) = 1$ for all $p|m$, then $(-m/q) = 1$.
-/
lemma exists_odd_sq_mod_prime_of_jacobi_eq_one (m q : ℕ) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b : ℤ, b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b % 2 = 1 := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℤ, b₀ ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
    haveI := Fact.mk hq_prime
    norm_num [← ZMod.intCast_eq_intCast_iff, jacobiSym] at *
    norm_num [Nat.primeFactorsList_prime hq_prime] at h_jacobi
    rw [legendreSym.eq_one_iff] at h_jacobi
    · obtain ⟨x, hx⟩ := h_jacobi
      exact ⟨x.val, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm⟩
    · rw [legendreSym] at h_jacobi
      aesop
  by_cases hb₀_odd : b₀ % 2 = 1
  · exact ⟨b₀, hb₀, hb₀_odd⟩
  · refine ⟨b₀ + q, ?_, ?_⟩ <;> simp_all +decide [Int.ModEq, ← even_iff_two_dvd, parity_simps]
    · simp +decide [← hb₀, ← ZMod.intCast_eq_intCast_iff']
    · norm_num [Int.add_emod, Int.even_iff.mp hb₀_odd,
        show (q : ℤ) % 2 = 1 from mod_cast hq_prime.eq_two_or_odd.resolve_left (by aesop_cat)]

lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_mod : q % 4 = 1)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    jacobiSym (-m) q = 1 := by
  -- We need to show that $(q/m) = (-2/m)$.
  have h_jacobi_qm : jacobiSym q m = jacobiSym (-2) m := by
    have h_jacobi_qm : jacobiSym (-2 * q) m = 1 := by
      rw [ jacobiSym ];
      rw [ List.prod_eq_one ] ;
      intro x a
      simp_all
      obtain ⟨w, h⟩ := a
      obtain ⟨w_1, h⟩ := h
      obtain ⟨left, right⟩ := w_1
      obtain ⟨left_1, right⟩ := right
      subst h
      haveI := Fact.mk left; simp_all +decide [jacobiSym ] ;
      specialize h_jacobi w left_1 left; simp_all +decide [ Nat.primeFactorsList_prime left ] ;
    rw [ jacobiSym.mul_left ] at h_jacobi_qm;
    rw [ Int.mul_eq_one_iff_eq_one_or_neg_one ] at h_jacobi_qm ; aesop;
  -- Since $(-m/q) = (q/m)$ and $(q/m) = (-2/m)$, we have $(-m/q) = (-2/m)$.
  have h_jacobi_neg_mq : jacobiSym (-m) q = jacobiSym q m := by
    rw [jacobiSym.neg _ (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_one_mod_four hq_mod, one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hq_mod
  rw [ h_jacobi_neg_mq, h_jacobi_qm, jacobiSym.mod_right ] ; norm_num [ hm_mod ];
  exact Nat.odd_iff.mpr ( by omega )

/-
There exist integers $b$ and $h$ such that $b$ is odd and $b^2 - 4qh = -m$.
-/
lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b % 2 = 1 ∧ b^2 - 4 * q * h = -m := by
  -- Since $(-m/q) = 1$, there exists an integer $b$ such that $b^2 \equiv -m \pmod{q}$.
  obtain ⟨b, hb_mod_q, hb_odd⟩ :=
    exists_odd_sq_mod_prime_of_jacobi_eq_one m q hq_prime hq_mod h_jacobi
  -- We need $b^2 \equiv -m \pmod{4q}$.
  have hb_mod : b ^ 2 ≡ -↑m [ZMOD (4 * ↑q : ℤ)] := by
    -- Since $q$ is odd, $4$ and $q$ are coprime. We can use the Chinese Remainder Theorem to combine the congruences $b^2 \equiv -m \pmod q$ and $b^2 \equiv -m \pmod 4$.
    have h_crt : b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b ^ 2 ≡ -↑m [ZMOD 4] := by
      exact ⟨ hb_mod_q, by rw [ ← Int.emod_add_mul_ediv b 2, hb_odd ] ; ring_nf; norm_num [ Int.ModEq, Int.add_emod, Int.sub_emod, Int.mul_emod ] ; omega ⟩;
    rw [ ← Int.modEq_and_modEq_iff_modEq_mul ] ; tauto;
    exact Nat.Coprime.symm ( hq_prime.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd ( by decide ) h; interval_cases q <;> trivial );
  exact ⟨ b, ( b^2 - ( -m ) ) / ( 4 * q ), hb_odd, by linarith [ Int.ediv_mul_cancel ( show ( 4 * q : ℤ ) ∣ b^2 - ( -m ) from hb_mod.symm.dvd ) ] ⟩

/-
There exists an integer $t$ such that $2q t^2 \equiv -1 \pmod m$.
-/
/-- Per-prime existence: for a prime `p` with `2q` coprime to `p` and `(-2q/p) = 1`, there is
an integer `t_p` with `2q·t_p² ≡ -1 (mod p)`. The witness is `s · (2q)⁻¹` where `s² ≡ -2q`. -/
private lemma exists_t_local_of_jacobi (p q : ℕ) (hp : Nat.Prime p)
    (hp_cop : Nat.Coprime (2 * q) p) (hjac : jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, 2 * q * t ^ 2 ≡ -1 [ZMOD p] := by
  haveI := Fact.mk hp
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s ^ 2 ≡ -2 * q [ZMOD p] := by
    simp_all +decide [jacobiSym, ← ZMod.intCast_eq_intCast_iff, Nat.primeFactorsList_prime hp]
    rw [legendreSym.eq_one_iff] at hjac
    · obtain ⟨x, hx⟩ := hjac
      refine ⟨x.val, ?_⟩
      simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
    · rw [legendreSym] at hjac
      aesop
  obtain ⟨inv_2q, hinv_2q⟩ : ∃ inv_2q : ℤ, (2 * q : ℤ) * inv_2q ≡ 1 [ZMOD p] := by
    have := Int.mod_coprime hp_cop
    push_cast at this
    exact this
  refine ⟨s * inv_2q, ?_⟩
  convert hs.mul_left (2 * q * inv_2q ^ 2) |>.trans ?_ using 1 <;> ring_nf
  convert (hinv_2q.pow 2).neg using 1
  ring

/-- If `m` is squarefree and an integer congruence `x ≡ y (mod p)` holds for every prime
factor `p` of `m`, then the congruence lifts to `x ≡ y (mod m)`. -/
private lemma int_modEq_of_forall_modEq_primeFactors_squarefree {m : ℕ} (hm : Squarefree m)
    {x y : ℤ} (h : ∀ p ∈ m.primeFactors, x ≡ y [ZMOD (p : ℤ)]) : x ≡ y [ZMOD m] := by
  rw [Int.modEq_iff_dvd]
  have h_prod : (m : ℤ) = ∏ p ∈ Nat.primeFactors m, (p : ℤ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm]
  rw [h_prod]
  refine Finset.prod_dvd_of_coprime (fun p hp q hq hpq => ?_)
    (fun p hp => Int.modEq_iff_dvd.mp (h p hp))
  have := Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)
  aesop

/-- Integer CRT over the prime factors of a squarefree number: given per-prime residue data,
produce a single integer matching all the congruences simultaneously. -/
private lemma exists_int_crt_primeFactors_squarefree {m : ℕ} (t : ℕ → ℤ) :
    ∃ x : ℤ, ∀ p ∈ m.primeFactors, x ≡ t p [ZMOD (p : ℤ)] := by
  -- Build indicator `x p` = `y_p · ∏_{q≠p} q · t p`, with `y_p · ∏ ≡ 1 (mod p)`.
  have h_ind : ∀ p ∈ m.primeFactors, ∃ x : ℤ, x ≡ t p [ZMOD (p : ℤ)] ∧
      ∀ q ∈ m.primeFactors, q ≠ p → x ≡ 0 [ZMOD (q : ℤ)] := by
    intro p hp
    obtain ⟨y_p, hy_p⟩ : ∃ y_p : ℤ, y_p * (∏ q ∈ m.primeFactors \ {p}, (q : ℤ)) ≡ 1 [ZMOD p] := by
      have h_coprime : Nat.gcd p (∏ q ∈ m.primeFactors \ {p}, q) = 1 :=
        Nat.Coprime.prod_right fun q hq => by
          have := Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1)
          aesop
      have h_bezout := Nat.gcd_eq_gcd_ab p (∏ q ∈ m.primeFactors \ {p}, q)
      refine ⟨Nat.gcdB p (∏ q ∈ m.primeFactors \ {p}, q), ?_⟩
      rw [Int.modEq_iff_dvd]
      refine ⟨Nat.gcdA p (∏ q ∈ m.primeFactors \ {p}, q), ?_⟩
      rw [h_coprime] at h_bezout
      push_cast at h_bezout ⊢
      linarith
    refine ⟨y_p * (∏ q ∈ m.primeFactors \ {p}, (q : ℤ)) * t p, by simpa using hy_p.mul_right _,
      fun q hq hqp => Int.modEq_zero_iff_dvd.mpr <|
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
          (Finset.dvd_prod_of_mem _ (by aesop)) _) _⟩
  choose! x hx₁ hx₂ using h_ind
  refine ⟨∑ p ∈ m.primeFactors, x p, fun p hp => ?_⟩
  -- `∑ = x p + ∑_{q ≠ p} x q ≡ x p + 0 ≡ t p (mod p)`.
  rw [← Finset.add_sum_erase _ _ hp]
  have h_rest : (p : ℤ) ∣ ∑ q ∈ m.primeFactors.erase p, x q :=
    Finset.dvd_sum fun q hq => by
      obtain ⟨hq_ne, hq_mem⟩ := Finset.mem_erase.mp hq
      exact Int.modEq_zero_iff_dvd.mp (hx₂ q hq_mem p hp (Ne.symm hq_ne))
  calc x p + ∑ q ∈ m.primeFactors.erase p, x q
      ≡ x p + 0 [ZMOD (p : ℤ)] := (Int.ModEq.refl _).add (Int.modEq_zero_iff_dvd.mpr h_rest)
    _ = x p := by ring
    _ ≡ t p [ZMOD (p : ℤ)] := hx₁ p hp

lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, (2 * q : ℤ) * t^2 ≡ -1 [ZMOD m] := by
  -- Per-prime data: every prime factor `p` of `m` is odd and `≠ q`.
  have h_tp : ∀ p ∈ Nat.primeFactors m, ∃ t_p : ℤ, 2 * q * t_p ^ 2 ≡ -1 [ZMOD (p : ℤ)] := by
    intro p hp
    refine exists_t_local_of_jacobi p q (Nat.prime_of_mem_primeFactors hp) ?_
      (h_jacobi p (Nat.dvd_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hp))
    refine Nat.Coprime.mul_left ?_ ?_
    · refine Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p => ?_
      have : 2 ∣ m := dvd_trans h2p (Nat.dvd_of_mem_primeFactors hp)
      omega
    · rw [Nat.coprime_primes hq_prime (Nat.prime_of_mem_primeFactors hp)]
      rintro rfl
      have := h_jacobi q (Nat.dvd_of_mem_primeFactors hp) hq_prime
      rw [jacobiSym.mod_left] at this
      norm_num at this
      rw [jacobiSym.zero_left hq_prime.one_lt] at this
      exact absurd this (by decide)
  choose! t ht using h_tp
  -- CRT: assemble a single integer `x` matching all `t p` modulo `p`.
  obtain ⟨x, hx⟩ := exists_int_crt_primeFactors_squarefree (m := m) t
  refine ⟨x, int_modEq_of_forall_modEq_primeFactors_squarefree hm_sq fun p hp => ?_⟩
  calc 2 * (q : ℤ) * x ^ 2 ≡ 2 * q * (t p) ^ 2 [ZMOD (p : ℤ)] := ((hx p hp).pow 2).mul_left _
    _ ≡ -1 [ZMOD (p : ℤ)] := ht p hp

noncomputable def linear_map_M (m q : ℕ) (t b : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (![![2 * t * q, t * b, m], ![(Real.sqrt (2 * q)), b / (Real.sqrt (2 * q)), 0], ![0, Real.sqrt m / Real.sqrt (2 * q), 0]] : Matrix (Fin 3) (Fin 3) ℝ)

lemma det_linear_map_M (m q : ℕ) (t b : ℤ) (_hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M m q t b) = m * Real.sqrt m := by
  unfold linear_map_M
  simp +decide [Matrix.det_fin_three]
  rw [mul_assoc, mul_div_cancel₀ _ (by positivity)]

lemma det_linear_map_M_ne_zero (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M m q t b) ≠ 0 := by
  rw [det_linear_map_M m q t b hm hq]
  positivity

noncomputable abbrev linear_map_M_euclidean (m q : ℕ) (t b : ℤ) : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)) :=
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

/-
The volume of the preimage of the ball is $\frac{4}{3}\pi (2m)^{3/2} / m^{3/2}$.
-/
lemma vol_preimage_ball_euclidean (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    MeasureTheory.volume ((linear_map_M_euclidean m q t b) ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m)))) = ENNReal.ofReal ((4 / 3) * Real.pi * (2 * m) ^ (3 / 2 : ℝ) / (m * Real.sqrt m)) := by
  -- The volume of the preimage is $\text{vol}(B(0, \sqrt{2m})) / |\det M|$.
  have h_volume : (MeasureTheory.volume ((⇑(linear_map_M_euclidean m q t b)) ⁻¹' (Metric.ball 0 (Real.sqrt (2 * ↑m))))) = (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * ↑m)))) / ENNReal.ofReal (abs (LinearMap.det (linear_map_M_euclidean m q t b))) := by
    have h_volume_image : ∀ {L : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3))}, LinearMap.det L ≠ 0 → ∀ {E : Set (EuclideanSpace ℝ (Fin 3))}, MeasurableSet E → MeasureTheory.volume (L ⁻¹' E) = MeasureTheory.volume E / ENNReal.ofReal (abs (LinearMap.det L)) := by
      intro L hL E hE; rw [ div_eq_mul_inv ] ; rw [ MeasureTheory.Measure.addHaar_preimage_linearMap ]
      simp_all only [ne_eq, abs_inv, abs_pos, not_false_eq_true, ENNReal.ofReal_inv_of_pos]
      · ring;
      · assumption;
    apply h_volume_image
    · rw [det_linear_map_M_euclidean m q t b hm hq]
      positivity
    · exact measurableSet_ball
  -- The volume of the ball of radius $\sqrt{2m}$ is $\frac{4}{3}\pi (\sqrt{2m})^3$.
  have h_ball_volume : (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * ↑m)))) = ENNReal.ofReal ((4 / 3) * Real.pi * (Real.sqrt (2 * ↑m)) ^ 3) := by
    norm_num +zetaDelta at *;
    rw [ ← ENNReal.ofReal_mul ( by positivity ), ← ENNReal.ofReal_pow ( by positivity ) ] ; ring_nf;
    rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf;
  -- The determinant of the linear map is $m^{3/2}$.
  have h_det : abs (LinearMap.det (linear_map_M_euclidean m q t b)) = m * Real.sqrt m := by
    convert congr_arg abs (det_linear_map_M_euclidean m q t b hm hq) using 1
    rw [ abs_of_nonneg ( by positivity ) ];
  rw [ h_volume, h_ball_volume, h_det, ENNReal.ofReal_div_of_pos ];
  · rw [ show ( Real.sqrt ( 2 * m ) ) ^ 3 = ( 2 * m ) ^ ( 3 / 2 : ℝ ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ];
  · positivity

/-
The calculated volume is greater than 8.
-/
lemma volume_inequality : (4 / 3) * Real.pi * (2 : ℝ) ^ (3 / 2 : ℝ) > 8 := by
  rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

lemma quad_form_decomposition (m q : ℕ) (b h x y : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
      (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 =
      2 * ((q : ℝ) * x ^ 2 + (b : ℝ) * x * y + (h : ℝ) * y ^ 2) := by
  have hsqrt_2q_pos : (Real.sqrt 2 * Real.sqrt q : ℝ) ≠ 0 := by positivity
  have hsqrt_m_sq : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)
  have hb2 : (b : ℝ) ^ 2 = 4 * q * h - m := by
    have h1 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
    exact_mod_cast h1
  have hb2' : (b : ℝ) ^ 2 + m = 4 * q * h := by linarith [hb2]
  field_simp [hsqrt_2q_pos]
  rw [show (Real.sqrt 2 : ℝ) ^ 2 = 2 by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)],
    show (Real.sqrt q : ℝ) ^ 2 = q by nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (q : ℝ))], hsqrt_m_sq]
  ring_nf
  nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), hb2', hb2]


/-- Minkowski volume certificate: the preimage under `linear_map_M_euclidean` of the ball
of radius `√(2m)` has volume strictly greater than `2^3 = 8`. This is the key numerical
input to Minkowski's convex-body theorem for producing a nonzero lattice point. -/
private lemma vol_preimage_ball_gt_eight (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    (2 : ENNReal) ^ 3 < MeasureTheory.volume
      ((linear_map_M_euclidean m q t b) ⁻¹'
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
  rw [vol_preimage_ball_euclidean m q t b hm hq]
  norm_num
  ring_nf
  field_simp
  ring_nf
  have : (m : ℝ) * √(m : ℝ) = (m : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt, (by norm_num : (3 : ℝ) = 2 + 1), Real.rpow_add]
    simp only [Real.rpow_ofNat, Nat.cast_nonneg, Real.sq_sqrt, Real.rpow_one]
    all_goals positivity
  rw [this, Real.mul_rpow, mul_comm π, mul_assoc, mul_assoc, mul_lt_mul_iff_right₀]
  · rw [← pow_lt_pow_iff_left₀ (n := 2)]
    · norm_num1
      rw [mul_pow, ← Real.rpow_two, ← Real.rpow_mul (by simp)]
      nlinarith [Real.pi_gt_d4]
    · simp
    · positivity
    · positivity
  all_goals positivity

/-- Explicit row-wise action of `linear_map_M_euclidean` on a Euclidean vector. -/
private lemma linear_map_M_euclidean_apply_coords (m q : ℕ) (t b : ℤ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (linear_map_M_euclidean m q t b x) 0 = 2 * t * q * x 0 + t * b * x 1 + m * x 2 ∧
    (linear_map_M_euclidean m q t b x) 1 =
      Real.sqrt (2 * q) * x 0 + b / Real.sqrt (2 * q) * x 1 ∧
    (linear_map_M_euclidean m q t b x) 2 = Real.sqrt m / Real.sqrt (2 * q) * x 1 := by
  unfold linear_map_M_euclidean
  norm_num [Fin.sum_univ_three]
  ring_nf
  erw [Matrix.toLin'_apply]
  ring_nf
  simp_all (config := { decide := true }) only [Fin.isValue]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Matrix.mulVec]
    ring_nf!
  · simp [Matrix.mulVec]
    ring!
  · simp (config := { decide := Bool.true }) [Matrix.mulVec]
    ring_nf
    aesop (simp_config := { decide := Bool.true })

private lemma exists_lattice_xyz_lt_two_m (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    let R := (2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z
    let S := Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y
    let T := Real.sqrt m / Real.sqrt (2 * q) * y
    R^2 + S^2 + T^2 < 2 * m := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))
  let S_pre := (linear_map_M_euclidean m q t b) ⁻¹' B
  have h_symm : ∀ x ∈ S_pre, -x ∈ S_pre := fun x hx => by
    simp only [S_pre, B, Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_neg, norm_neg]
      at hx ⊢
    exact hx
  have h_conv : Convex ℝ S_pre :=
    Convex.linear_preimage (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) _
  have h_vol : (2 : ENNReal) ^ 3 < MeasureTheory.volume S_pre :=
    vol_preimage_ball_gt_eight m q t b hm hq
  let E := EuclideanSpace ℝ (Fin 3)
  have := classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure h_symm h_conv h_vol
  obtain ⟨x, hx0, hxs, h⟩ := this
  have hcoor0 := h 0
  have hcoor1 := h 1
  have hcoor2 := h 2
  obtain ⟨R, hr⟩ := hcoor0
  obtain ⟨S, hs⟩ := hcoor1
  obtain ⟨T, ht⟩ := hcoor2
  use R, S, T
  constructor
  · contrapose! hx0
    ext i
    fin_cases i <;> aesop
  · convert ( show ( ‖linear_map_M_euclidean m q t b x‖ ^ 2 : ℝ ) < 2 * m from ?_ ) using 1 <;> norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] ; ring_nf
    simp_all only [Nat.ofNat_nonneg, Real.sqrt_mul, Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_neg,
      norm_neg, implies_true, ne_eq, Fin.isValue, Real.sq_sqrt, Nat.cast_nonneg, inv_pow, S_pre, B]
    · have h_expand := linear_map_M_euclidean_apply_coords m q t b x
      rw [ Real.sq_sqrt <| by positivity ]
      have heq : ∀ i, (linear_map_M m q t b) ((EuclideanSpace.equiv (Fin 3) ℝ) x) i =
          ((linear_map_M_euclidean m q t b) x).ofLp i := fun _ => rfl
      simp only [heq]
      rw [ h_expand.1, h_expand.2.1, h_expand.2.2 ]
      ring_nf
      norm_num [ ne_of_gt, hq, hm ]
      ring_nf
      norm_num [ hq.ne', hm.ne' ]
      ring
    · simp +zetaDelta at *
      rw [ EuclideanSpace.norm_eq ] at hxs
      simp_all only [Fin.isValue, Real.norm_eq_abs, sq_abs]
      rw [ Real.sq_sqrt <| by positivity ]
      rw [ ← Real.sqrt_mul <| by positivity ] at *
      rw [ Real.sqrt_lt_sqrt_iff <| by positivity ] at *
      norm_num [ Fin.sum_univ_three ] at *
      linarith!

private lemma rst_expand_eq (m q : ℕ) (t b h x y z : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
      (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 =
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) := by
  have hqf :=
    congrArg
      (fun u : ℝ => (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 + u)
      (quad_form_decomposition m q b h x y hq hbqm)
  calc
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
        (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
        (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2
        = (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
            ((Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
              (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2) := by ring
    _ = (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
          2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) := by
          simpa [add_assoc, add_left_comm, add_comm] using hqf

/-- Key composite identity: under `t²·2q ≡ -1 (mod m)` and `b² - 4qh = -m`,
we have `t²·b² ≡ -2h (mod m)`. Combines the two hypotheses: `b² ≡ 4qh (mod m)` from `hbqm`,
and `t²·2q ≡ -1` turns `t²·(4qh) = (t²·2q)·(2h)` into `-2h`. -/
private lemma t_sq_mul_b_sq_modEq_neg_two_h {m q : ℕ} {t b h : ℤ}
    (hqt : t ^ 2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    t ^ 2 * b ^ 2 ≡ -2 * h [ZMOD m] := by
  have hb_sq : b ^ 2 = 4 * q * h - m := by linarith
  calc t ^ 2 * b ^ 2
      = t ^ 2 * (4 * q * h - m) := by rw [hb_sq]
    _ = (t ^ 2 * 2 * q) * (2 * h) - t ^ 2 * m := by ring
    _ ≡ (-1) * (2 * h) - 0 [ZMOD m] := (hqt.mul_right _).sub
        (Int.modEq_zero_iff_dvd.mpr ⟨t ^ 2, by ring⟩)
    _ = -2 * h := by ring

private lemma rst_modEq_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : t^2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) ≡ 0 [ZMOD m] := by
  -- Algebraic expansion: sum-of-squares = `P(t,q,b,h,x,y) + M(t,q,b,x,y,z) · m`, so mod `m`
  -- it suffices to reduce the polynomial `P` using `hqt` and `t²·b² ≡ -2h`.
  have htb2 := t_sq_mul_b_sq_modEq_neg_two_h hqt (by exact_mod_cast hbqm)
  calc (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
        2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2)
      = (t ^ 2 * 2 * q) * (x * b * y * 2) + (t ^ 2 * 2 * q) * (q * x ^ 2 * 2) +
          t ^ 2 * b ^ 2 * y ^ 2 + (q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2) +
          (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m := by ring
    _ ≡ (-1) * (x * b * y * 2) + (-1) * (q * x ^ 2 * 2) +
          (-2 * h) * y ^ 2 + (q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2) + 0 [ZMOD m] := by
        refine Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add ?_ ?_) ?_)
          (Int.ModEq.refl _)) ?_
        · exact hqt.mul_right _
        · exact hqt.mul_right _
        · exact htb2.mul_right _
        · exact Int.modEq_zero_iff_dvd.mpr ⟨t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2,
            by ring⟩
    _ = 0 := by ring

/-- A real sum of three squares is zero iff each square is zero. -/
private lemma sq_eq_zero_of_sum_three_sq (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    a ^ 2 = 0 ∧ b ^ 2 = 0 ∧ c ^ 2 = 0 :=
  ⟨by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c],
   by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c],
   by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]⟩

private lemma xyz_zero_of_sum_sq_eq_zero (m q : ℕ) (t b x y z : ℤ)
    (hm : 0 < m) (hq : 0 < q)
    (hsum0 :
      (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
        (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
        (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  obtain ⟨hR0sq, hS0sq, hT0sq⟩ := sq_eq_zero_of_sum_three_sq _ _ _ hsum0
  have hy0 : y = 0 := by
    have hT0 : (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y : ℝ) = 0 := by nlinarith [hT0sq]
    have hcoef : (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) : ℝ) ≠ 0 := by positivity
    exact_mod_cast (mul_eq_zero.mp hT0).resolve_left hcoef
  have hx0 : x = 0 := by
    have hS0 : (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y : ℝ)
        = 0 := by nlinarith [hS0sq]
    have hcoef : (Real.sqrt 2 * Real.sqrt q : ℝ) ≠ 0 := by positivity
    have hlin : (Real.sqrt 2 * Real.sqrt q : ℝ) * x = 0 := by
      simpa [show (y : ℝ) = 0 from by exact_mod_cast hy0] using hS0
    exact_mod_cast (mul_eq_zero.mp hlin).resolve_left hcoef
  have hz0 : z = 0 := by
    have hR0 : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) = 0 := by nlinarith [hR0sq]
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hlin : (m : ℝ) * z = 0 := by
      simpa [show (x : ℝ) = 0 from by exact_mod_cast hx0,
        show (y : ℝ) = 0 from by exact_mod_cast hy0] using hR0
    exact_mod_cast (mul_eq_zero.mp hlin).resolve_left hmne
  exact ⟨hx0, hy0, hz0⟩



/-- The integer binary quadratic form `q·x² + b·x·y + h·y²` is nonnegative when its
discriminant is `-m < 0` (i.e. negative definite `-Δ`) and `q > 0`. -/
private lemma quadform_nonneg {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (x y : ℤ) :
    0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := by
  have hm_nn : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y), sq_nonneg (y : ℤ), hbqm]

/-- The binary form `q·x² + b·x·y + h·y²` with `q > 0` and discriminant `-m < 0` has only the
trivial zero: `qf = 0 ↔ x = y = 0`. (Reverse direction is trivial; stated as `x = 0 ∧ y = 0`.) -/
private lemma quadform_eq_zero_imp_xy_zero {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) {x y : ℤ}
    (h_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · refine ⟨?_, hy⟩
    subst hy; nlinarith [sq_nonneg x, hq, h_zero]
  · exfalso
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y), mul_self_pos.mpr hy, hbqm]

/-- A nonnegative integer `n ≡ 0 (mod m)` with `n < 2m` is either `0` or `m`. -/
private lemma eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul {m : ℤ} (hm : 0 < m)
    {n : ℤ} (h_nn : 0 ≤ n) (h_mod : n ≡ 0 [ZMOD m]) (h_lt : n < 2 * m) :
    n = 0 ∨ n = m := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h_mod
  have : 0 ≤ k := by nlinarith
  have : k < 2 := by nlinarith
  interval_cases k
  · left; linarith
  · right; linarith

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
    have h_expand : ((2 * t * q * x + t * b * y + m * z : ℤ) : ℝ) ^ 2 +
        2 * (((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 : ℤ) : ℝ) =
        (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
          (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
          (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 := by
      push_cast
      rw [← rst_expand_eq m q t b h x y z hq (by simpa using hbqm)]
      simp [mul_assoc, mul_left_comm, mul_comm]
    exact_mod_cast h_expand ▸ hlt
  have h_cases := eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul
    (by exact_mod_cast hm : (0 : ℤ) < m) (by positivity)
    (rst_modEq_zero m q t b h x y z hqt hbqm) h_lt
  rcases h_cases with h_case1 | h_case2
  · -- `R² + 2v = 0` forces `x = y = z = 0`, contradicting `(x, y, z) ≠ (0, 0, 0)`.
    have hsum0 : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
        (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
        (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0 := by
      rw [rst_expand_eq m q t b h x y z hq (by simpa using hbqm)]
      exact_mod_cast h_case1
    obtain ⟨rfl, rfl, rfl⟩ := xyz_zero_of_sum_sq_eq_zero m q t b x y z hm hq hsum0
    exact absurd rfl hne
  · refine' ⟨ x, y, 2 * t * q * x + t * b * y + m * z, Int.toNat ( q * x ^ 2 + b * x * y + h * y ^ 2 ), _, _, _ ⟩ <;> norm_num;
    · nlinarith [ sq_nonneg ( 2 * q * x + b * y ) ];
    · rw [ max_eq_left ];
      · convert h_case2 using 1;
      · nlinarith [ sq_nonneg ( 2 * q * x + b * y ) ];
    · contrapose! hne
      have hqf_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
        nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y)]
      obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm hqf_zero
      simp_all +decide
      rcases m with _ | _ | m <;> norm_num at *
      · refine absurd (congr_arg (· % 4) hbqm) ?_
        norm_num [sq, Int.add_emod, Int.sub_emod, Int.mul_emod]
        have := Int.emod_nonneg b four_pos.ne'
        have := Int.emod_lt_of_pos b four_pos
        interval_cases b % 4 <;> trivial
      · nlinarith [show z ^ 2 * (m + 1 + 1) = 1 by nlinarith]

/-- There exist q, b, h, t, x, y, z yielding R² + 2v = m with v > 0 -/
lemma exists_R_v_of_mod8_eq3 (m : ℕ) (hm : Squarefree m) (hm_pos : 0 < m) (hmod : m % 8 = 3) :
    ∃ (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ),
      Nat.Prime q ∧ q % 4 = 1 ∧
      (∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) ∧
      b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ) ∧
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨q, hq_prime, hq_mod, hjac⟩ := exists_prime_aux m hm hmod
  obtain ⟨b, h, _, hbqm⟩ := exists_b_h m q hmod hq_prime hq_mod (jacobi_neg_m_q m q hmod hq_mod hjac)
  obtain ⟨t, hqt⟩ := exists_t m q hm hmod hq_prime hjac
  have hqt' : t ^ 2 * 2 * q ≡ -1 [ZMOD m] := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hqt
  obtain ⟨x, y, R, v, hv_def, hRv, hv_pos⟩ :=
    exists_Rv_from_Minkowski m q t b h hm_pos (hq_prime.pos) hqt' hbqm
  exact ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩

lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ)
    (hp : Nat.Prime p) (_hp_odd : p ≠ 2)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  haveI := Fact.mk hp
  rw [jacobiSym]
  norm_num [Nat.primeFactorsList_prime hp]
  simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd, legendreSym.eq_one_iff]
  use a / b'
  grind

lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : ¬ Even (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  induction' n : Int.natAbs a + Int.natAbs b' using Nat.strong_induction_on with n ih generalizing a b'
  by_cases h_div_b' : (p : ℤ) ∣ b'
  · obtain ⟨k, hk⟩ := h_div_b'
    obtain ⟨a', ha'⟩ : ∃ a', a = p * a' := by
      have h_div_a : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2 := by
        contrapose! h_odd_val
        rw [padicValInt.eq_zero_of_not_dvd h_odd_val]
        norm_num
      exact Int.Prime.dvd_pow' hp <| by simpa [hk, ← ZMod.intCast_zmod_eq_zero_iff_dvd] using h_div_a
    contrapose! ih
    refine' ⟨_, _, a', k, _, rfl, ih⟩
    · rcases eq_or_ne a' 0 with ha0 | ha0 <;> rcases eq_or_ne k 0 with hk0 | hk0 <;>
        simp_all +decide [Int.natAbs_mul]
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hk0) hp.one_lt
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr ha0) hp.one_lt
      · nlinarith [hp.two_le, abs_pos.mpr ha0, abs_pos.mpr hk0]
    · simp_all +decide [padicValInt, parity_simps]
      rw [show (p * a') ^ 2 + d * (p * k) ^ 2 = p ^ 2 * (a' ^ 2 + d * k ^ 2) by ring,
        Int.natAbs_mul, Int.natAbs_pow] at h_odd_val
      haveI := Fact.mk hp
      rw [padicValNat.mul] at h_odd_val <;> simp_all +decide [parity_simps]
      · exact hp.ne_zero
      · intro H
        simp_all +decide
  · apply jacobi_neg_d_of_dvd_sq_add p a d b' hp hp_odd
    · contrapose! h_odd_val
      rw [padicValInt.eq_zero_of_not_dvd h_odd_val]
      norm_num
    · exact hp_not_dvd_d
    · exact h_div_b'

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
  haveI := Fact.mk hp
  simp_all +decide [← ZMod.intCast_eq_intCast_iff, jacobiSym,
    Nat.primeFactorsList_prime hp]
  rw [legendreSym.eq_one_iff]
  · exact ⟨R, by simpa [sq] using hRa.symm⟩
  · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpa

lemma p_mod4_eq1_of_dvd_v_not_dvd_m (p : ℕ) (q : ℤ) (b h x y v R m : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -m)
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : ¬ Even (padicValInt p v))
    (hpm : ¬ (p : ℤ) ∣ m) :
    p % 4 = 1 := by
  have h_jacobi_m : jacobiSym m p = 1 := by
    refine jacobiSym_eq_one_of_sq_modEq hp hpm (R := R) ?_
    -- `R² ≡ m (mod p)`: from `R² + 2v = m` and `p ∣ v` (⟸ `v ≠ 0 mod p` since padic val odd).
    have hpv : (p : ℤ) ∣ v := by
      contrapose! hpv
      simp_all +decide [padicValInt.eq_zero_of_not_dvd]
    refine Int.modEq_iff_dvd.mpr ?_
    rw [show (m - R ^ 2 : ℤ) = 2 * v by linarith]
    exact hpv.mul_left 2
  have h_jacobi_neg_m : jacobiSym (-m) p = 1 := by
    by_cases hpq : (p : ℤ) ∣ q <;> simp_all
    · have hb_sq_mod_p : b ^ 2 ≡ -m [ZMOD p] := by
        exact Int.modEq_iff_dvd.mpr ⟨-4 * h * hpq.choose, by linear_combination -hbqm - 4 * h * hpq.choose_spec⟩
      haveI := Fact.mk hp
      simp_all +decide [← ZMod.intCast_eq_intCast_iff, jacobiSym]
      simp_all +decide [Nat.primeFactorsList_prime hp]
      rw [legendreSym.eq_one_iff] at *
      · exact ⟨b, by simpa [sq] using hb_sq_mod_p.symm⟩
      · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpm
      · simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    · have h_jacobi_neg_m_odd : ¬ Even (padicValInt p ((2 * q * x + b * y) ^ 2 + m * y ^ 2)) := by
        have h_jacobi_neg_m_odd : padicValInt p (4 * q * v) = padicValInt p v := by
          haveI := Fact.mk hp
          rw [padicValInt.mul, padicValInt.mul] <;> norm_num
          · exact ⟨Or.inr <| mod_cast fun h => hp_odd <| by have := Nat.le_of_dvd (by decide) h; interval_cases p <;> trivial,
              Or.inr <| Or.inr hpq⟩
          · aesop
          · aesop_cat
          · aesop
        grind
      apply jacobi_neg_d_of_odd_padicVal p (2 * q * x + b * y) m y hp hp_odd hpm h_jacobi_neg_m_odd
  have h_jacobi_neg_1 : jacobiSym (-1) p = 1 := by
    have h_mul : jacobiSym (-m) p = jacobiSym (-1) p * jacobiSym m p := by
      simpa [neg_mul] using (jacobiSym.mul_left (-1) m p)
    rw [h_mul, h_jacobi_m] at h_jacobi_neg_m
    simpa using h_jacobi_neg_m
  rw [jacobiSym.at_neg_one] at h_jacobi_neg_1
  · rw [ZMod.χ₄_nat_mod_four] at h_jacobi_neg_1
    have := Nat.mod_lt p zero_lt_four
    interval_cases p % 4 <;> trivial
  · exact hp.odd_of_ne_two hp_odd

lemma p_mod4_of_dvd_v_dvd_m (p : ℕ) (q : ℕ) (b h x y : ℤ) (R v : ℤ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3)
    (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m)
    (hjac : jacobiSym (-2 * q) p = 1) :
    False := by
  have hp_R : (p : ℤ) ∣ R := by
    exact Int.Prime.dvd_pow' hp <| by
      rw [← Int.dvd_add_left (dvd_mul_of_dvd_right hpv _)]
      exact hRv.symm ▸ Int.natCast_dvd_natCast.mpr hpm
  have hp_2qx_by : (p : ℤ) ∣ (2 * q * x + b * y) := by
    have h_sum : (p : ℤ) ∣ ((2 * q * x + b * y) ^ 2 + m * y ^ 2) := by
      rw [← four_q_v_eq_sq_plus_m_y_sq hv hbqm]
      exact hpv.mul_left (4 * q)
    have hpm_int : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
    have h_sq : (p : ℤ) ∣ (2 * q * x + b * y) ^ 2 :=
      (Int.dvd_add_left (hpm_int.mul_right _)).mp h_sum
    exact Int.Prime.dvd_pow' hp h_sq
  have h_y_sq_mod_p : y ^ 2 ≡ 2 * q [ZMOD p] := by
    have h_div_p : (m / p : ℤ) * y ^ 2 ≡ (m / p : ℤ) * (2 * q) [ZMOD p] := by
      have h_div_p : (4 * q * v : ℤ) ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
        obtain ⟨k, hk⟩ := hpv
        simp_all +decide [Int.modEq_iff_dvd]
        obtain ⟨a, ha⟩ := hp_R
        obtain ⟨b', hb'⟩ := hp_2qx_by
        simp_all +decide [← eq_sub_iff_add_eq', ← mul_assoc]
        exact ⟨a ^ 2 * 2 * q, by nlinarith⟩
      have h_div_p : (4 * q * v : ℤ) ≡ (2 * q * x + b * y) ^ 2 + m * y ^ 2 [ZMOD p ^ 2] := by
        exact Int.modEq_of_dvd ⟨0, by rw [hv]; linear_combination' hbqm * y ^ 2⟩
      have h_div_p : (m : ℤ) * y ^ 2 ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
        simp_all +decide [Int.ModEq]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at *
        aesop
      rw [Int.modEq_iff_dvd] at *
      obtain ⟨k, hk⟩ := h_div_p
      use k
      nlinarith [hp.two_le, Int.ediv_mul_cancel (show (p : ℤ) ∣ m from mod_cast hpm)]
    haveI := Fact.mk hp
    simp_all +decide [← ZMod.intCast_eq_intCast_iff]
    cases h_div_p <;> simp_all +decide [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_cast at *
    simp_all +decide [Nat.squarefree_iff_prime_squarefree]
  have h_jacobi_2q_p : jacobiSym (2 * q) p = 1 := by
    refine jacobiSym_eq_one_of_sq_modEq hp ?_ (R := y) h_y_sq_mod_p
    intro h2q
    have hdvd_neg : (p : ℤ) ∣ (-2 * (q : ℤ)) := by
      have : (-2 * (q : ℤ)) = -(2 * q) := by ring
      rw [this]; exact h2q.neg_right
    rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd hdvd_neg,
      jacobiSym.zero_left hp.one_lt] at hjac
    exact absurd hjac (by decide)
  haveI := Fact.mk hp
  simp_all +decide [jacobiSym.mul_left, ← ZMod.intCast_eq_intCast_iff]
  rw [jacobiSym.neg] at hjac
  · rw [ZMod.χ₄_nat_mod_four] at hjac
    simp_all +decide [jacobiSym.mul_left]
  · exact hp.odd_of_ne_two <| by aesop_cat

lemma even_padicVal_of_mod4_eq3 (p : ℕ) (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3)
    (hm_sq : Squarefree m)
    (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → jacobiSym (-2 * ↑q) ↑p' = 1) :
    Even (padicValNat p (2 * v)) := by
  by_cases hp2 : p = 2
  · aesop
  · by_cases hpv : (p : ℤ) ∣ v
    · by_cases hpm : (p : ℕ) ∣ m
      · have := p_mod4_of_dvd_v_dvd_m p q b h x y R v m hp hp3 hm_sq hv_def hbqm hRv hpv hpm (hjac p hpm hp)
        aesop
      · have h_contradiction : ¬ Even (padicValInt p v) → False := by
          intro h_odd
          have := p_mod4_eq1_of_dvd_v_not_dvd_m p q b h x y v R m hp hp2 hv_def hbqm hRv
            (by exact h_odd) (by exact_mod_cast hpm)
          cases this.symm.trans hp3
        simp_all +decide [padicValNat.mul, hv_pos.ne']
        simp_all [← hv_def]
        rw [padicValNat.eq_zero_of_not_dvd] <;> simp_all +decide [Nat.prime_dvd_prime_iff_eq]
    · rw [padicValNat.eq_zero_of_not_dvd] <;> norm_num
      exact fun h => hpv <| Int.natCast_dvd_natCast.mpr <| hp.dvd_mul.mp h |> Or.resolve_left <| by
        intro t
        have := Nat.le_of_dvd (by positivity) t
        interval_cases p <;> trivial

lemma two_v_sum_two_squares (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hm_sq : Squarefree m)
    (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) :
    ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro p hp hp3
  exact even_padicVal_of_mod4_eq3 p q b h x y R v m (Nat.prime_of_mem_primeFactors hp) hp3
    hm_sq hv_pos hv_def hbqm hRv hjac


/-- The final theorem -/
theorem blueprint_case_mod8_eq3 (m : ℕ) (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hm_mod : m % 8 = 3) : IsSumOfThreeSquares m := by
  obtain ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩ :=
    exists_R_v_of_mod8_eq3 m hm_sq hm_pos hm_mod
  have h2v := two_v_sum_two_squares q b h x y R v m hm_sq hv_pos hv_def hbqm hRv hjac
  have habc : ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
    grind +qlia
  obtain ⟨a, b, c, habc⟩ := habc
  refine ⟨a.natAbs, b.natAbs, c.natAbs, ?_⟩
  apply Int.ofNat.inj
  calc
    ((a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 : ℕ) : ℤ)
        = a ^ 2 + b ^ 2 + c ^ 2 := by
          norm_num [Int.natCast_natAbs, sq_abs]
    _ = (m : ℤ) := by simpa using habc.symm
end
