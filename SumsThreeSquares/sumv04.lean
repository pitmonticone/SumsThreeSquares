import Mathlib
import SumsThreeSquares.minkowskiconvex


open scoped BigOperators

open scoped Real Int

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

/-
A number is the sum of three squares if it can be written as a^2 + b^2 + c^2.
-/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

#check Squarefree

/-
There exists a prime $q$ such that $q \equiv 1 \pmod 4$ and $(-2q/p) = 1$ for all prime factors $p$ of $m$.
-/


lemma exists_prime_aux (m : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  -- By Dirichlet's theorem on arithmetic progressions, there exists a prime $q$ in the residue class $a \pmod{4m}$, where $a$ is chosen such that $(-2q/p) = 1$ for all primes $p$ dividing $m$.
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → jacobiSym (-2 * a) p = 1) ∧ a % 4 = 1 ∧ Nat.gcd a (4 * m) = 1 := by
    -- For each prime $p$ dividing $m$, choose $a_p$ such that $(-2a_p/p) = 1$.
    have ha_p : ∀ p : ℕ, p ∣ m → Nat.Prime p → ∃ a_p : ℕ, jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 ∧ a_p % 4 = 1 := by
      intro p hp hp_prime
      obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 := by
        by_cases hp_two : p = 2;
        · simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          omega;
        · -- Since $p$ is odd, we can choose $a_p$ such that $-2a_p$ is a quadratic residue modulo $p$.
          obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 := by
            have h_quad_res : ∃ x : ℕ, jacobiSym x p = 1 ∧ x % p ≠ 0 := by
              exact ⟨ 1, by norm_num [ jacobiSym ], by norm_num [ Nat.mod_eq_of_lt hp_prime.two_le ] ⟩
            obtain ⟨ x, hx₁, hx₂ ⟩ := h_quad_res;
            -- Since $-2$ is invertible modulo $p$, we can choose $a_p$ such that $-2a_p \equiv x \pmod{p}$.
            obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, -2 * a_p ≡ x [ZMOD p] := by
              have h_inv : ∃ y : ℤ, -2 * y ≡ 1 [ZMOD p] := by
                have h_inv : Int.gcd (-2 : ℤ) p = 1 := by
                  exact Nat.coprime_comm.mp ( hp_prime.coprime_iff_not_dvd.mpr fun h => hp_two <| by have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> trivial );
                norm_num +zetaDelta at *;
                have := Int.gcd_eq_gcd_ab 2 p;
                exact ⟨ -Int.gcdA 2 p, Int.modEq_iff_dvd.mpr ⟨ Int.gcdB 2 p, by linarith ⟩ ⟩;
              obtain ⟨ y, hy ⟩ := h_inv;
              exact ⟨ Int.toNat ( y * x % p ), by rw [ Int.toNat_of_nonneg ( Int.emod_nonneg _ <| Nat.cast_ne_zero.mpr hp_prime.ne_zero ) ] ; simpa [ ← ZMod.intCast_eq_intCast_iff, mul_assoc ] using hy.mul_right x ⟩;
            refine' ⟨ a_p, _, _ ⟩;
            · rw [ jacobiSym.mod_left ] at *;
              rw [ ha_p ] ; aesop;
            · intro h; haveI := Fact.mk hp_prime; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
              simp_all +decide [ ← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff ];
          use a_p;
      -- Since $a_p \not\equiv 0 \pmod{p}$, we can choose $k$ such that $a_p + kp \equiv 1 \pmod{4}$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (a_p + k * p) % 4 = 1 := by
        norm_num [ Nat.add_mod, Nat.mul_mod ];
        have := Nat.mod_lt a_p zero_lt_four; have := Nat.mod_lt p zero_lt_four; interval_cases _ : a_p % 4 <;> interval_cases _ : p % 4 <;> simp_all +decide;
        all_goals have := Nat.Prime.eq_two_or_odd hp_prime; simp_all +decide [ ← Nat.mod_mod_of_dvd p ( by decide : 2 ∣ 4 ) ];
        any_goals omega;
        exacts [ ⟨ 1, rfl ⟩, ⟨ 3, rfl ⟩, ⟨ 0, rfl ⟩, ⟨ 0, rfl ⟩, ⟨ 3, rfl ⟩, ⟨ 1, rfl ⟩, ⟨ 2, rfl ⟩, ⟨ 2, rfl ⟩ ];
      refine' ⟨ a_p + k * p, _, _, hk ⟩ <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
      rw [ show ( - ( 2 * ( a_p + k * p ) ) : ℤ ) = - ( 2 * a_p ) + ( - ( 2 * k * p ) ) by ring, jacobiSym.mod_left ] ;
      simp_all only [dvd_refl, Nat.mod_mod_of_dvd, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod,
        Int.add_neg_mul_emod_self_right]
      obtain ⟨left, right⟩ := ha_p
      rw [ eq_comm, jacobiSym.mod_left ] at * ; aesop;
    choose! a ha using ha_p;
    -- By the Chinese Remainder Theorem, there exists an integer $a$ such that $a \equiv a_p \pmod{p}$ for each prime $p$ dividing $m$, and $a \equiv 1 \pmod{4}$.
    obtain ⟨a_crt, ha_crt⟩ : ∃ a_crt : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → a_crt ≡ a p [MOD p]) ∧ a_crt ≡ 1 [MOD 4] := by
      have h_crt : ∃ a_crt : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → a_crt ≡ a p [MOD p]) ∧ (a_crt ≡ 1 [MOD 4]) := by
        have h_crt_exists : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p ∧ p ∣ m) → ∃ a_crt : ℕ, (∀ p ∈ S, a_crt ≡ a p [MOD p]) ∧ (a_crt ≡ 1 [MOD 4]) := by
          intro S hS; induction' S using Finset.induction with p S hS ih; aesop;
          obtain ⟨ a_crt, ha_crt₁, ha_crt₂ ⟩ := ih fun q hq => hS q ( Finset.mem_insert_of_mem hq );
          -- We need to find an integer $x$ such that $x \equiv a_crt \pmod{4 \prod_{q \in S} q}$ and $x \equiv a_p \pmod{p}$.
          obtain ⟨x, hx⟩ : ∃ x : ℕ, x ≡ a_crt [MOD 4 * Finset.prod S id] ∧ x ≡ a p [MOD p] := by
            have h_crt : Nat.gcd (4 * Finset.prod S id) p = 1 := by
              refine' Nat.Coprime.mul_left _ _;
              · have := hS p ( Finset.mem_insert_self _ _ ) ; rcases this with ⟨ hp₁, hp₂ ⟩ ; exact Nat.Coprime.pow_left 2 ( Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by have := Nat.mod_eq_zero_of_dvd h; have := Nat.mod_eq_zero_of_dvd ( dvd_trans h hp₂ ) ; omega ) ;
              · exact Nat.Coprime.prod_left fun q hq => Nat.coprime_comm.mp <| hS p ( Finset.mem_insert_self _ _ ) |>.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ S› <| by have := Nat.prime_dvd_prime_iff_eq ( hS p ( Finset.mem_insert_self _ _ ) |>.1 ) ( hS q ( Finset.mem_insert_of_mem hq ) |>.1 ) ; aesop;
            have := Nat.chineseRemainder h_crt;
            exact ⟨ _, this a_crt ( a p ) |>.2 ⟩;
          use x;
          norm_num +zetaDelta at *;
          exact ⟨ ⟨ hx.2, fun q hq => hx.1.of_dvd ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ hq ) _ ) |> Nat.ModEq.trans <| ha_crt₁ q hq ⟩, hx.1.of_dvd ( dvd_mul_right _ _ ) |> Nat.ModEq.trans <| ha_crt₂ ⟩
        specialize @h_crt_exists ( Nat.primeFactors m ) ; aesop;
      exact h_crt;
    refine' ⟨ a_crt, _, _, _ ⟩;
    · intro p hp hp_prime; specialize ha p hp hp_prime; specialize ha_crt; have := ha_crt.1 p hp hp_prime; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
      haveI := Fact.mk hp_prime; simp_all +decide [jacobiSym ] ;
      simp_all +decide [ Nat.primeFactorsList_prime hp_prime ];
      simp_all +decide [ legendreSym ];
    · exact ha_crt.2;
    · refine' Nat.Coprime.mul_right _ _;
      · exact ha_crt.2.gcd_eq.trans ( by norm_num );
      · refine' Nat.coprime_of_dvd' _;
        intro k hk hk₁ hk₂; have := ha_crt.1 k hk₂ hk; simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ] ;
  -- Since $a$ is coprime to $4m$, by Dirichlet's theorem on arithmetic progressions, there exists a prime $q$ in the residue class $a \pmod{4m}$.
  obtain ⟨q, hq⟩ : ∃ q : ℕ, Nat.Prime q ∧ q % (4 * m) = a % (4 * m) ∧ q % 4 = 1 := by
    -- By Dirichlet's theorem on arithmetic progressions, there are infinitely many primes in the residue class $a \pmod{4m}$.
    have h_dirichlet : Set.Infinite {q : ℕ | Nat.Prime q ∧ q % (4 * m) = a % (4 * m)} := by
      have := @Nat.setOf_prime_and_eq_mod_infinite;
      specialize @this ( 4 * m ) ?_ ( a : ZMod ( 4 * m ) ) ?_ <;>
      simp_all only [Int.reduceNeg, neg_mul]
      · exact ⟨ by aesop_cat ⟩;
      · obtain ⟨left, middle, right⟩ := ha
        exact (ZMod.isUnit_iff_coprime a (4 * m)).mpr right;
      · convert this using 1;
        norm_num [ ← ZMod.natCast_eq_natCast_iff' ];
    cases' h_dirichlet.exists_gt ( 4 * m ) with q hq ; use q ;
    simp_all only [Int.reduceNeg, neg_mul, Set.mem_setOf_eq, true_and]
    obtain ⟨left, right⟩ := ha
    obtain ⟨left_1, right_1⟩ := hq
    obtain ⟨left_2, right⟩ := right
    obtain ⟨left_1, right_2⟩ := left_1
    rw [ ← Nat.mod_mod_of_dvd q ( dvd_mul_right 4 m ), right_2, Nat.mod_mod_of_dvd _ ( dvd_mul_right 4 m ), left_2 ];
  refine' ⟨ q, hq.left, hq.right.right, fun p hp hp' => _ ⟩;
  -- Since $q \equiv a \pmod{4m}$, we have $(-2q/p) = (-2a/p)$.
  have h_cong : jacobiSym (-2 * (q : ℤ)) p = jacobiSym (-2 * (a : ℤ)) p := by
    have h_cong : q ≡ a [ZMOD p] := by
      exact Int.ModEq.of_dvd ( Int.natCast_dvd_natCast.mpr ( dvd_mul_of_dvd_right hp 4 ) ) ( Int.natCast_modEq_iff.mpr hq.2.1 );
    rw [ jacobiSym.mod_left, jacobiSym.mod_left ];
    rw [ Int.ModEq.mul_left _ h_cong ];
    simp +decide [jacobiSym.mod_left ];
  aesop

/-
If $m \equiv 3 \pmod 8$ is squarefree, $q \equiv 1 \pmod 4$ is prime, and $(-2q/p) = 1$ for all $p|m$, then $(-m/q) = 1$.
-/
lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
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
    rw [ jacobiSym.quadratic_reciprocity ] ;
    simp_all only [Int.reduceNeg, neg_mul]
    · rw [ jacobiSym.neg ] ; norm_num [ Nat.even_div, hq_mod ] ; ring_nf;
      · erw [ show ( q : ZMod 4 ) = 1 by erw [ ZMod.natCast_eq_natCast_iff ] ; norm_num [ Nat.ModEq, hq_mod ] ] ; norm_num;
      · exact hq_prime.odd_of_ne_two <| by aesop_cat;
    · exact hq_prime.odd_of_ne_two <| by aesop_cat;
    · exact Nat.odd_iff.mpr ( by omega );
  rw [ h_jacobi_neg_mq, h_jacobi_qm, jacobiSym.mod_right ] ; norm_num [ hm_mod ];
  exact Nat.odd_iff.mpr ( by omega )

/-
There exist integers $b$ and $h$ such that $b$ is odd and $b^2 - 4qh = -m$.
-/
lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b % 2 = 1 ∧ b^2 - 4 * q * h = -m := by
  -- Since $(-m/q) = 1$, there exists an integer $b$ such that $b^2 \equiv -m \pmod{q}$.
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b % 2 = 1 := by
    -- Since $(-m/q) = 1$, there exists an integer $b_0$ such that $b_0^2 \equiv -m \pmod q$.
    obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℤ, b₀ ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
      haveI := Fact.mk hq_prime; norm_num [ ← ZMod.intCast_eq_intCast_iff, jacobiSym ] at *;
      norm_num [ Nat.primeFactorsList_prime hq_prime ] at h_jacobi;
      rw [ legendreSym.eq_one_iff ] at h_jacobi;
      · obtain ⟨ x, hx ⟩ := h_jacobi; use x.val; simpa [ sq, ← ZMod.intCast_eq_intCast_iff ] using hx.symm;
      · rw [ legendreSym ] at h_jacobi ; aesop;
    by_cases hb₀_odd : b₀ % 2 = 1;
    · use b₀;
    · refine' ⟨ b₀ + q, _, _ ⟩ <;> simp_all +decide [ Int.ModEq, ← even_iff_two_dvd, parity_simps ];
      · simp +decide [ ← hb₀, ← ZMod.intCast_eq_intCast_iff' ];
      · norm_num [ Int.add_emod, Int.even_iff.mp hb₀_odd, show ( q : ℤ ) % 2 = 1 from mod_cast hq_prime.eq_two_or_odd.resolve_left ( by aesop_cat ) ];
  -- We need $b^2 \equiv -m \pmod{4q}$.
  have hb_mod : b ^ 2 ≡ -↑m [ZMOD (4 * ↑q : ℤ)] := by
    -- Since $q$ is odd, $4$ and $q$ are coprime. We can use the Chinese Remainder Theorem to combine the congruences $b^2 \equiv -m \pmod q$ and $b^2 \equiv -m \pmod 4$.
    have h_crt : b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b ^ 2 ≡ -↑m [ZMOD 4] := by
      exact ⟨ hb.1, by rw [ ← Int.emod_add_mul_ediv b 2, hb.2 ] ; ring_nf; norm_num [ Int.ModEq, Int.add_emod, Int.sub_emod, Int.mul_emod ] ; omega ⟩;
    rw [ ← Int.modEq_and_modEq_iff_modEq_mul ] ; tauto;
    exact Nat.Coprime.symm ( hq_prime.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd ( by decide ) h; interval_cases q <;> trivial );
  exact ⟨ b, ( b^2 - ( -m ) ) / ( 4 * q ), hb.2, by linarith [ Int.ediv_mul_cancel ( show ( 4 * q : ℤ ) ∣ b^2 - ( -m ) from hb_mod.symm.dvd ) ] ⟩

/-
There exists an integer $t$ such that $2q t^2 \equiv -1 \pmod m$.
-/
lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, (2 * q : ℤ) * t^2 ≡ -1 [ZMOD m] := by
  -- By the Chinese Remainder Theorem, there exists $t$ such that $t \equiv t_p \pmod p$ for all $p|m$.
  obtain ⟨t, ht⟩ : ∃ t : ℤ, ∀ p ∈ Nat.primeFactors m, 2 * q * t ^ 2 ≡ -1 [ZMOD p] := by
    -- For each prime $p$ dividing $m$, there exists an integer $t_p$ such that $2q t_p^2 \equiv -1 \pmod p$.
    have h_exists_tp (p : ℕ) (hp : p ∈ Nat.primeFactors m) : ∃ t_p : ℤ, 2 * q * t_p ^ 2 ≡ -1 [ZMOD p] := by
      -- Since $(-2q/p) = 1$, there exists an integer $t$ such that $t^2 \equiv -2q \pmod p$.
      obtain ⟨t, ht⟩ : ∃ t : ℤ, t ^ 2 ≡ -2 * q [ZMOD p] := by
        haveI := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; simp_all +decide [ jacobiSym, ← ZMod.intCast_eq_intCast_iff ] ;
        specialize h_jacobi p hp.2.1 hp.1 ; simp_all +decide [ Nat.primeFactorsList_prime hp.1 ];
        rw [ legendreSym.eq_one_iff ] at h_jacobi;
        · obtain ⟨ x, hx ⟩ := h_jacobi; use x.val; simpa [ sq, ← ZMod.intCast_eq_intCast_iff ] using hx.symm;
        · rw [ legendreSym ] at h_jacobi ; aesop;
      -- Let $t_p = t \cdot (2q)^{-1}$, where $(2q)^{-1}$ is the multiplicative inverse of $2q$ modulo $p$.
      obtain ⟨inv_2q, hinv_2q⟩ : ∃ inv_2q : ℤ, 2 * q * inv_2q ≡ 1 [ZMOD p] := by
        have h_inv : Int.gcd (2 * q : ℤ) p = 1 := by
          refine' Nat.Coprime.mul_left _ _;
          · simp_all only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq, Int.natAbs_cast, Nat.coprime_two_left]
            obtain ⟨left, right⟩ := hp
            obtain ⟨left_1, right⟩ := right
            apply Odd.of_dvd_nat _ left_1
            rw [Nat.odd_iff]
            omega
          · rw [ Nat.coprime_primes ] <;>
            simp_all only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq, Int.natAbs_cast]
            obtain ⟨left, right⟩ := hp
            obtain ⟨left_1, right⟩ := right
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only
            have := h_jacobi q left_1 left; rw [ jacobiSym.mod_left ] at this; norm_num at this;
            rw [ jacobiSym.zero_left ] at this ; aesop;
            exact left.one_lt;
        exact Int.mod_coprime h_inv;
      use t * inv_2q;
      convert ht.mul_left ( 2 * q * inv_2q ^ 2 ) |> Int.ModEq.trans <| ?_ using 1 <;> ring_nf;
      convert hinv_2q.pow 2 |> Int.ModEq.neg using 1 ; ring;
    choose! t ht using h_exists_tp;
    have h_crt : ∀ p ∈ m.primeFactors, ∃ x : ℤ, x ≡ t p [ZMOD p] ∧ ∀ q ∈ m.primeFactors, q ≠ p → x ≡ 0 [ZMOD q] := by
      -- For each prime factor $p$ of $m$, let $y_p$ be the multiplicative inverse of $\prod_{q \in m.primeFactors, q \neq p} q$ modulo $p$.
      intros p hp
      obtain ⟨y_p, hy_p⟩ : ∃ y_p : ℤ, y_p * (∏ q ∈ m.primeFactors \ {p}, (q : ℤ)) ≡ 1 [ZMOD p] := by
        have h_coprime : Nat.gcd p (∏ q ∈ m.primeFactors \ {p}, q) = 1 := by
          exact Nat.Coprime.prod_right fun q hq => by have := Nat.coprime_primes ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors ( Finset.mem_sdiff.mp hq |>.1 ) ) ; aesop;
        have := Nat.gcd_eq_gcd_ab p ( ∏ q ∈ m.primeFactors \ { p }, q )
        simp_all only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq, and_imp, Nat.cast_one, Nat.cast_prod,
          not_false_eq_true, neg_add_rev, forall_const, implies_true]
        obtain ⟨left, right⟩ := hp
        obtain ⟨left_1, right⟩ := right
        exact ⟨ Nat.gcdB p ( ∏ q ∈ m.primeFactors \ { p }, q ), by rw [ Int.modEq_iff_dvd ] ; use Nat.gcdA p ( ∏ q ∈ m.primeFactors \ { p }, q ) ; linarith ⟩;
      use y_p * (∏ q ∈ m.primeFactors \ {p}, (q : ℤ)) * t p;
      exact ⟨ by simpa using hy_p.mul_right _, fun q hq hqp => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
    choose! x hx₁ hx₂ using h_crt;
    use ∑ p ∈ m.primeFactors, x p;
    simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
    intro p pp dp dm; rw [ Finset.sum_eq_single p ] <;> aesop;
  -- Since $m$ is squarefree, $m = \prod p$, so $2q t^2 \equiv -1 \pmod m$.
  use t;
  -- Since $m$ is squarefree, it is the product of its distinct prime factors.
  have h_prod : (m : ℤ) = ∏ p ∈ Nat.primeFactors m, (p : ℤ) := by
    rw [ ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm_sq ];
  simp_all +decide [ Int.modEq_iff_dvd ];
  exact Finset.prod_dvd_of_coprime ( fun p hp q hq hpq => by have := Nat.coprime_primes ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ; aesop ) fun p hp => ht p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ( by aesop_cat )

/-
The determinant of the linear map is $m\sqrt{m}$.
-/
noncomputable def linear_map_M (m q : ℕ) (t b : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (![![2 * t * q, t * b, m], ![(Real.sqrt (2 * q)), b / (Real.sqrt (2 * q)), 0], ![0, Real.sqrt m / Real.sqrt (2 * q), 0]] : Matrix (Fin 3) (Fin 3) ℝ)

lemma det_linear_map_M (m q : ℕ) (t b : ℤ) (_hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M m q t b) = m * Real.sqrt m := by
  unfold linear_map_M;
  simp +decide [ Matrix.det_fin_three ];
  rw [ mul_assoc, mul_div_cancel₀ _ ( by positivity ) ]

/-
The determinant of the linear map is non-zero.
-/
lemma det_linear_map_M_ne_zero (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M m q t b) ≠ 0 := by
  rw [ det_linear_map_M m q t b hm hq ]
  positivity

#check MeasureTheory.volume

#check (dist : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)

/-
The linear map corresponding to the matrix M.
-/
noncomputable def linear_map_M_euclidean (m q : ℕ) (t b : ℤ) : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)) :=
  (Matrix.toLin' (![![2 * t * q, t * b, m], ![(Real.sqrt (2 * q)), b / (Real.sqrt (2 * q)), 0], ![0, Real.sqrt m / Real.sqrt (2 * q), 0]] : Matrix (Fin 3) (Fin 3) ℝ))

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
    apply h_volume_image; exact (by
    convert det_linear_map_M_ne_zero m q t b hm hq); exact measurableSet_ball;
  -- The volume of the ball of radius $\sqrt{2m}$ is $\frac{4}{3}\pi (\sqrt{2m})^3$.
  have h_ball_volume : (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * ↑m)))) = ENNReal.ofReal ((4 / 3) * Real.pi * (Real.sqrt (2 * ↑m)) ^ 3) := by
    norm_num +zetaDelta at *;
    rw [ ← ENNReal.ofReal_mul ( by positivity ), ← ENNReal.ofReal_pow ( by positivity ) ] ; ring;
    rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring;
  -- The determinant of the linear map is $m^{3/2}$.
  have h_det : abs (LinearMap.det (linear_map_M_euclidean m q t b)) = m * Real.sqrt m := by
    convert congr_arg abs ( det_linear_map_M m q t b hm hq ) using 1;
    rw [ abs_of_nonneg ( by positivity ) ];
  rw [ h_volume, h_ball_volume, h_det, ENNReal.ofReal_div_of_pos ];
  · rw [ show ( Real.sqrt ( 2 * m ) ) ^ 3 = ( 2 * m ) ^ ( 3 / 2 : ℝ ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ];
  · positivity

/-
The volume of the preimage of the ball is $\frac{4}{3}\pi (2m)^{3/2} / m^{3/2}$.
-/
noncomputable def mapM (m q : ℕ) (t b : ℤ) : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)) :=
  (Matrix.toLin' (![![2 * t * q, t * b, m], ![(Real.sqrt (2 * q)), b / (Real.sqrt (2 * q)), 0], ![0, Real.sqrt m / Real.sqrt (2 * q), 0]] : Matrix (Fin 3) (Fin 3) ℝ))

lemma det_mapM (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (mapM m q t b) = m * Real.sqrt m := by
      convert det_linear_map_M m q t b hm hq using 1

lemma vol_preimage_ball_mapM (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    MeasureTheory.volume ((mapM m q t b) ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m)))) = ENNReal.ofReal ((4 / 3) * Real.pi * (2 * m) ^ (3 / 2 : ℝ) / (m * Real.sqrt m)) := by
      convert vol_preimage_ball_euclidean m q t b hm hq using 1

/-
The volume of a ball of radius $r$ in $\mathbb{R}^3$ is $\frac{4}{3}\pi r^3$.
-/
lemma volume_ball_fin3 (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) = ENNReal.ofReal ((4 / 3) * Real.pi * r ^ 3) := by
      erw [ MeasureTheory.Measure.addHaar_ball ] ; norm_num ; ring;
      · rw [ ← ENNReal.ofReal_mul ( by positivity ), mul_assoc ];
      · positivity

/-
The determinant of the linear map is $m\sqrt{m}$.
-/
lemma det_linear_map_M_euclidean (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linear_map_M_euclidean m q t b) = m * Real.sqrt m := by
      convert det_mapM m q t b hm hq

/-
The volume of the preimage of the ball is $\frac{4}{3}\pi (2m)^{3/2} / m^{3/2}$.
-/
lemma vol_preimage_ball_euclidean_v3 (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    MeasureTheory.volume ((linear_map_M_euclidean m q t b) ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m)))) = ENNReal.ofReal ((4 / 3) * Real.pi * (2 * m) ^ (3 / 2 : ℝ) / (m * Real.sqrt m)) := by
      convert vol_preimage_ball_mapM m q t b hm hq using 1

/-
The calculated volume is greater than 8.
-/
lemma volume_inequality : (4 / 3) * Real.pi * (2 : ℝ) ^ (3 / 2 : ℝ) > 8 := by
  rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-!
## Main Theorem Structure

Following the proof in content.tex, we break the main theorem into cases based on m mod 8.
The proof structure follows Davenport's method using Minkowski's theorem.
-/

/-
Step 1: By Minkowski's theorem, there exist integers x₁, y₁, z₁ (not all zero) such that
R₁² + S₁² + T₁² < 2m, where R, S, T are defined by the linear map.
-/

lemma exists_lattice_xyz (m q : ℕ) (t b : ℤ) (h : ℤ) (hm : 0 < m) (hq : 0 < q) (hqt : t^2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * q * h = -m) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    let R := (2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z
    let S := Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y
    let T := Real.sqrt m / Real.sqrt (2 * q) * y
    R^2 + S^2 + T^2 = m := by

  have : ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    let R := (2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z
    let S := Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y
    let T := Real.sqrt m / Real.sqrt (2 * q) * y
    R^2 + S^2 + T^2 < 2 * m := by
      let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))
      -- Define the preimage S under the linear map M
      let S_pre := (mapM m q t b) ⁻¹' B

      -- Step 1: Show S_pre is symmetric
      have h_symm : ∀ x ∈ S_pre, -x ∈ S_pre := by
        intro x hx
        unfold S_pre B at hx ⊢
        simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hx ⊢
        rw [map_neg, norm_neg]
        exact hx

      -- Step 2: Show S_pre is convex
      have h_conv : Convex ℝ S_pre := by
        unfold S_pre
        apply Convex.linear_preimage
        exact convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))

      -- Step 3: Show the volume condition 2³ < volume(S_pre)
      have h_vol : (2 : ENNReal) ^ 3 < MeasureTheory.volume S_pre := by
        unfold S_pre
        rw [vol_preimage_ball_mapM m q t b hm hq]
        norm_num
        ring_nf
        -- Need to show: 8 < (4/3) * π * (2m)^(3/2) / (m√m)
        field_simp
        ring_nf
        have : (m : ℝ) * √(m : ℝ) = (m : ℝ) ^ (3 / 2 : ℝ) := by
          rw [Real.rpow_div_two_eq_sqrt, (by norm_num : (3  : ℝ) = 2 + 1), Real.rpow_add]
          simp only [Real.rpow_ofNat, Nat.cast_nonneg, Real.sq_sqrt, Real.rpow_one]
          all_goals positivity
        rw [this, Real.mul_rpow, mul_comm π, mul_assoc, mul_assoc, mul_lt_mul_iff_right₀];
        · rw [← pow_lt_pow_iff_left₀ (n := 2)]
          · norm_num1
            rw [mul_pow, ← Real.rpow_two, ← Real.rpow_mul (by simp)]
            nlinarith [Real.pi_gt_d4]
          · simp
          · positivity
          · positivity
        all_goals positivity





      let E := EuclideanSpace ℝ (Fin 3)
      -- define s as the volume bounded by x^2 + y^2 + z^3 ≤ 2*m
      --We need
      ---h_symm, h_conv, h
      --let s : Set E := {X | ‖X‖^2 < 2 * m}
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
      · contrapose! hx0; ext i; fin_cases i <;> aesop
      · convert ( show ( ‖mapM m q t b x‖ ^ 2 : ℝ ) < 2 * m from ?_ ) using 1 <;> norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] ; ring_nf ;
        simp_all only [Nat.ofNat_nonneg, Real.sqrt_mul, Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_neg,
          norm_neg, implies_true, ne_eq, Fin.isValue, Real.sq_sqrt, Nat.cast_nonneg, inv_pow, S_pre, B]
        · -- By definition of matrix multiplication and the properties of the Euclidean norm, we can expand the right-hand side.
          have h_expand : (mapM m q t b x) 0 = 2 * t * q * x 0 + t * b * x 1 + m * x 2 ∧ (mapM m q t b x) 1 = Real.sqrt (2 * q) * x 0 + b / Real.sqrt (2 * q) * x 1 ∧ (mapM m q t b x) 2 = Real.sqrt m / Real.sqrt (2 * q) * x 1 := by
            unfold mapM; norm_num [ Fin.sum_univ_three ] ; ring_nf;
            erw [ Matrix.toLin'_apply ] ; ring_nf ;
            simp_all (config := { decide := true }) only [Fin.isValue]
            apply And.intro
            · norm_num [ Matrix.mulVec ] ; ring_nf!;
            · apply And.intro
              · simp [Matrix.mulVec];
                ring!;
              · simp ( config := { decide := Bool.true } ) [ Matrix.mulVec] ; ring_nf ; aesop ( simp_config := { decide := Bool.true } ) ;
          rw [ Real.sq_sqrt <| by positivity ] ; rw [ h_expand.1, h_expand.2.1, h_expand.2.2 ] ; ring_nf ; norm_num [ ne_of_gt, hq, hm ] ; ring_nf;
          norm_num [ hq.ne', hm.ne' ] ; ring;
        · simp +zetaDelta at *;
          rw [ EuclideanSpace.norm_eq ] at hxs ;
          simp_all only [Fin.isValue, Real.norm_eq_abs, sq_abs]
          rw [ Real.sq_sqrt <| by positivity ] ; rw [ ← Real.sqrt_mul <| by positivity ] at * ; rw [ Real.sqrt_lt_sqrt_iff <| by positivity ] at * ; norm_num [ Fin.sum_univ_three ] at * ; linarith!;

  obtain ⟨x,y,z,hx0,hRST⟩ := this
  use x, y, z
  simp [hx0]

  have : let R := (2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z
    let S := Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y
    let T := Real.sqrt m / Real.sqrt (2 * q) * y
    R^2 + S^2 + T^2  = R^2 + 2 * (q*x^2 + b*x*y +h*y^2) := by
      simp
      rw [add_assoc, add_left_cancel_iff]
      field_simp
      repeat rw [Real.sq_sqrt (by positivity : 0 ≤ (q : ℝ))]
      repeat rw [Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ))]
      repeat rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
      ring_nf!
      repeat rw [add_assoc]
      rw [add_left_cancel_iff]
      have : (b : ℝ)^2 = 4 * q * h - m  := by
        have h1 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
        exact_mod_cast h1
      rw [this]
      ring_nf!



  simp at this
  rw [this]
  have : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 + 2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) ≡ 0 [ZMOD m] := by
    ring_nf!
    have : t * ↑q * x * ↑m * z * 4 + t * b * y * ↑m * z * 2 + t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 + ↑m ^ 2 * z ^ 2 = t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 + (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m := by ring_nf
    rw [this]
    -- The term (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m is divisible by m
    have hdiv : (m : ℤ) ∣ (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m := dvd_mul_left _ _
    -- So the whole expression is congruent to the first part mod m
    have hmodeq : t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 + (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m
        ≡ t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := by
      have h0 : (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m ≡ 0 [ZMOD m] :=
        Int.modEq_zero_iff_dvd.mpr hdiv
      calc t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
            ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 + (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m
          ≡ t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
            ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 + 0 [ZMOD m] :=
              Int.ModEq.add (Int.ModEq.refl _) h0
        _ = t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
            ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 := by ring
    calc t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 + (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m
        ≡ t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := hmodeq
      _ ≡ (t ^ 2 * 2 * ↑q) * x * b * y * 2 + (t ^ 2 * 2 * (q : ℤ)) * ↑q * x ^ 2 * 2 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2  [ZMOD m] := by ring_nf; simp
      -- Use hqt : t ^ 2 * 2 * ↑q ≡ -1 [ZMOD ↑m] to substitute
      _ ≡ (-1) * x * b * y * 2 + (-1) * ↑q * x ^ 2 * 2 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := by
        apply Int.ModEq.add
        apply Int.ModEq.add
        apply Int.ModEq.add
        apply Int.ModEq.add
        apply Int.ModEq.add
        · have : t ^ 2 * 2 * ↑q * x * b * y * 2 = (t ^ 2 * 2 * ↑q) * (x * b * y * 2) := by ring
          rw [this]
          have : (-1 : ℤ) * x * b * y * 2 = (-1) * (x * b * y * 2) := by ring
          rw [this]
          exact hqt.mul_right _
        · have : t ^ 2 * 2 * ↑q * ↑q * x ^ 2 * 2 = (t ^ 2 * 2 * ↑q) * (↑q * x ^ 2 * 2) := by ring
          rw [this]
          have : (-1 : ℤ) * ↑q * x ^ 2 * 2 = (-1) * (↑q * x ^ 2 * 2) := by ring
          rw [this]
          exact hqt.mul_right _
        all_goals exact Int.ModEq.refl _
      -- Simplify: -2*x*b*y - 2*q*x^2 + t^2*b^2*y^2 + 2*q*x^2 + 2*x*b*y + 2*h*y^2
      -- = t^2*b^2*y^2 + 2*h*y^2 = y^2 * (t^2*b^2 + 2*h)
      _ = t ^ 2 * b ^ 2 * y ^ 2 + y ^ 2 * h * 2 := by ring
      -- Now we need t^2 * b^2 + 2*h ≡ 0 (mod m)
      -- From hqt: t^2 * 2 * q ≡ -1 (mod m), so t^2 * b^2 * 2 * q ≡ -b^2 (mod m)
      -- From hbqm: b^2 = 4*q*h - m, so b^2 ≡ 4*q*h (mod m)
      -- So t^2 * b^2 * 2 * q ≡ -4*q*h (mod m)
      -- Thus t^2 * b^2 ≡ -2*h (mod m) (dividing by 2*q, which is valid if gcd(2q, m) = 1)
      _ ≡ 0 [ZMOD m] := by
        -- Use t^2 * 2 * q ≡ -1 and b^2 = 4*q*h - m
        have hb2 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
        -- t^2 * b^2 ≡ t^2 * (4*q*h - m) ≡ t^2 * 4 * q * h (mod m)
        have ht2b2 : t ^ 2 * b ^ 2 ≡ t ^ 2 * (4 * q * h) [ZMOD m] := by
          calc t ^ 2 * b ^ 2 = t ^ 2 * (4 * q * h - m) := by rw [hb2]
            _ = t ^ 2 * (4 * q * h) - t ^ 2 * m := by ring
            _ ≡ t ^ 2 * (4 * q * h) - 0 [ZMOD m] := by
                apply Int.ModEq.sub (Int.ModEq.refl _)
                exact Int.modEq_zero_iff_dvd.mpr ⟨t^2, by ring⟩
            _ = t ^ 2 * (4 * q * h) := by ring
        -- t^2 * 4 * q * h = (t^2 * 2 * q) * 2 * h ≡ -1 * 2 * h = -2*h (mod m)
        have ht2_4qh : t ^ 2 * (4 * q * h) ≡ -2 * h [ZMOD m] := by
          calc t ^ 2 * (4 * q * h) = (t ^ 2 * 2 * q) * (2 * h) := by ring
            _ ≡ (-1) * (2 * h) [ZMOD m] := hqt.mul_right _
            _ = -2 * h := by ring
        -- So t^2 * b^2 ≡ -2*h (mod m)
        calc t ^ 2 * b ^ 2 * y ^ 2 + y ^ 2 * h * 2
            ≡ (t ^ 2 * (4 * q * h)) * y ^ 2 + y ^ 2 * h * 2 [ZMOD m] := by
              apply Int.ModEq.add _ (Int.ModEq.refl _)
              exact ht2b2.mul_right _
          _ ≡ (-2 * h) * y ^ 2 + y ^ 2 * h * 2 [ZMOD m] := by
              apply Int.ModEq.add _ (Int.ModEq.refl _)
              exact ht2_4qh.mul_right _
          _ = 0 := by ring
  -- Now we know R^2 + 2*(q*x^2 + b*x*y + h*y^2) ≡ 0 (mod m) where R = 2*t*q*x + t*b*y + m*z
  -- So R^2 + S^2 + T^2 ≡ 0 (mod m)
  -- But R^2 + S^2 + T^2 < 2m and R^2 + S^2 + T^2 ≥ 0
  -- So R^2 + S^2 + T^2 ∈ {0, m}
  -- Since (x,y,z) ≠ (0,0,0), we need to show R^2 + S^2 + T^2 > 0 hence = m

  -- The goal is now to show R^2 + S^2 + T^2 = m
  -- We have:
  -- 1. this : (2*t*q*x + t*b*y + m*z)^2 + 2*(q*x^2 + b*x*y + h*y^2) ≡ 0 [ZMOD m]
  -- 2. hRST : R^2 + S^2 + T^2 < 2*m (from Minkowski)
  -- 3. R^2 + S^2 + T^2 ≥ 0 (sum of squares)
  -- 4. hx0 : (x,y,z) ≠ (0,0,0)

  -- First, show that R^2 + S^2 + T^2 is a multiple of m in ℝ
  -- Since R^2 + S^2 + T^2 = R^2 + 2*(q*x^2 + b*x*y + h*y^2) and this ≡ 0 (mod m) as integers
  -- we need to connect the real and integer worlds

  -- The expression (2*t*q*x + t*b*y + m*z)^2 + 2*(q*x^2 + b*x*y + h*y^2) is an integer
  -- Get k and show 0 ≤ k < 2
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp this

  -- The real version equals the integer version cast to ℝ
  have hreal : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 + 2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) =
               ((2 * t * ↑q * x + t * b * y + ↑m * z) ^ 2 + 2 * (↑q * x ^ 2 + b * x * y + h * y ^ 2) : ℤ) := by
    push_cast; ring

  -- So R^2 + S^2 + T^2 = k * m as reals
  have hkm : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 + 2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) = k * m := by
    rw [hreal, hk]; push_cast; ring

  -- Since R^2 + S^2 + T^2 ≥ 0, we have k * m ≥ 0, so k ≥ 0 (since m > 0)
  have hk_nonneg : 0 ≤ k := by
    have h1 : (0 : ℝ) ≤ (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 + 2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) := by
      -- The first term is a square, so ≥ 0
      -- The expression equals R^2 + S^2 + T^2 which is ≥ 0
      have hRST' : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
                   (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
                   (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 < 2 * m := hRST
      have heq : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 + 2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) =
                 (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
                 (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
                 (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 := by
        -- This follows from: S^2 + T^2 = 2*(q*x^2 + b*x*y + h*y^2)
        have hST : (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
                   (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 =
                   2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) := by
          have hsqrt_2q_pos : Real.sqrt (2 * q) ≠ 0 := by positivity
          have hsqrt_2q_sq : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by positivity)
          have hsqrt_m_sq : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)
          have hb2 : (b : ℝ)^2 = 4 * q * h - m := by
            have h1 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
            exact_mod_cast h1
          field_simp
          rw [hsqrt_2q_sq, hsqrt_m_sq]
          -- Goal: (2*q*x + b*y)^2 + y^2*m = 2*(2*q)*(x*(q*x + b*y) + y^2*h)
          -- Expand: 4*q^2*x^2 + 4*q*x*b*y + b^2*y^2 + m*y^2 = 4*q*(q*x^2 + b*x*y + h*y^2)
          -- = 4*q^2*x^2 + 4*q*b*x*y + 4*q*h*y^2
          -- So we need: b^2*y^2 + m*y^2 = 4*q*h*y^2
          -- i.e. b^2 + m = 4*q*h
          -- But we have b^2 = 4*q*h - m, so b^2 + m = 4*q*h ✓
          have hb2' : (b : ℝ)^2 + m = 4 * q * h := by linarith [hb2]
          ring_nf
          nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), hb2', hb2]
        linarith [hST]
      rw [heq]
      have h1 : 0 ≤ (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 := sq_nonneg _
      linarith
    rw [hkm] at h1
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) ≤ k * m := h1
    exact_mod_cast (mul_nonneg_iff_of_pos_right hm_pos).mp this

  -- Since R^2 + S^2 + T^2 < 2*m, we have k * m < 2 * m, so k < 2
  have hk_lt_2 : k < 2 := by
    have h1 : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 + 2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) < 2 * m := by
      convert hRST using 1
      -- Need: R^2 + S^2 + T^2 = R^2 + 2*(q*x^2 + b*x*y + h*y^2)
      -- i.e., S^2 + T^2 = 2*(q*x^2 + b*x*y + h*y^2)
      have hsqrt_2q_pos : Real.sqrt (2 * q) ≠ 0 := by positivity
      have hsqrt_2q_sq : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by positivity)
      have hsqrt_m_sq : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)
      have hb2 : (b : ℝ)^2 = 4 * q * h - m := by
        have h1 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
        exact_mod_cast h1
      have hb2' : (b : ℝ)^2 + m = 4 * q * h := by linarith [hb2]
      simp only [add_assoc]
      congr 1
      field_simp
      rw [hsqrt_2q_sq, hsqrt_m_sq]
      ring_nf
      nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), hb2', hb2]
    rw [hkm] at h1
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have : (k : ℝ) * m < 2 * m := h1
    have : (k : ℝ) < 2 := by nlinarith
    exact_mod_cast this

  -- So k ∈ {0, 1}
  interval_cases k
  · sorry
  · sorry
