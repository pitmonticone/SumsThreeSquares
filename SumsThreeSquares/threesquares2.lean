import Mathlib
import SumsThreeSquares.minkowskiconvex
open scoped BigOperators Real Int Nat Classical Pointwise
set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
noncomputable section
/-!
# Skeleton for the proof that m ≡ 3 (mod 8), squarefree ⟹ m is sum of three squares
This follows Davenport's proof. The key steps after establishing R₁² + 2v = m are:
1. Show that every odd prime p ≡ 3 (mod 4) divides v to an even power
2. Conclude 2v is a sum of two squares
3. Conclude m = R₁² + a² + b² is a sum of three squares
-/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n
/-! ## Algebraic identity -/
/-- Key equation: 4qv = (2qx + by)² + my² -/
lemma four_q_v_eq (q : ℤ) (b h x y : ℤ) (m : ℤ)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    4 * q * (q * x ^ 2 + b * x * y + h * y ^ 2) = (2 * q * x + b * y) ^ 2 + m * y ^ 2 := by
  grind
/-! ## Odd prime valuation analysis -/
/-
If p | (a² + d·b²) and p ∤ d, then either p | gcd(a,b) or (-d) is a QR mod p
-/
lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  haveI := Fact.mk hp;
  rw [ jacobiSym ];
  norm_num [ Nat.primeFactorsList_prime hp ];
  simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, legendreSym.eq_one_iff ];
  use a / b';
  grind
/-
If padicValInt p (a² + d·b²) is odd and p ∤ d, then (-d/p) = 1.
    This follows by descent: extract p-powers from a and b until p doesn't divide b.
-/
lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : ¬ Even (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  -- Use strong induction on the sum |a| + |b'|.
  induction' n : Int.natAbs a + Int.natAbs b' using Nat.strong_induction_on with n ih generalizing a b';
  by_cases h_div_b' : (p : ℤ) ∣ b';
  · obtain ⟨ k, hk ⟩ := h_div_b';
    -- Since $p$ divides $a$, we can write $a = p * a'$ for some integer $a'$.
    obtain ⟨ a', ha' ⟩ : ∃ a', a = p * a' := by
      have h_div_a : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2 := by
        contrapose! h_odd_val;
        rw [ padicValInt.eq_zero_of_not_dvd h_odd_val ] ; norm_num;
      exact Int.Prime.dvd_pow' hp <| by simpa [ hk, ← ZMod.intCast_zmod_eq_zero_iff_dvd ] using h_div_a;
    contrapose! ih;
    refine' ⟨ _, _, a', k, _, rfl, ih ⟩;
    · rcases eq_or_ne a' 0 <;> rcases eq_or_ne k 0 <;> simp_all +decide [ Int.natAbs_mul ];
      · exact n ▸ lt_mul_of_one_lt_left ( Int.natAbs_pos.mpr ‹_› ) hp.one_lt;
      · exact n ▸ lt_mul_of_one_lt_left ( Int.natAbs_pos.mpr ‹_› ) hp.one_lt;
      · nlinarith [ hp.two_le, abs_pos.mpr ‹a' ≠ 0›, abs_pos.mpr ‹k ≠ 0› ];
    · simp_all +decide [ padicValInt, parity_simps ];
      rw [ show ( p * a' ) ^ 2 + d * ( p * k ) ^ 2 = p ^ 2 * ( a' ^ 2 + d * k ^ 2 ) by ring, Int.natAbs_mul, Int.natAbs_pow ] at h_odd_val;
      haveI := Fact.mk hp; rw [ padicValNat.mul ] at h_odd_val <;> simp_all +decide [ parity_simps ] ;
      · exact hp.ne_zero;
      · intro H; simp_all +decide [ padicValNat.eq_zero_of_not_dvd, hp.ne_one, hp.ne_zero ] ;
  · apply jacobi_neg_d_of_dvd_sq_add p a d b' hp hp_odd;
    · contrapose! h_odd_val;
      rw [ padicValInt.eq_zero_of_not_dvd h_odd_val ] ; norm_num;
    · assumption;
    · assumption
/-
If p | v and p ∤ m, and R² + 2v = m, then p ≡ 1 (mod 4).
    Proof: From R² + 2v = m, (m/p) = 1. From 4qv = e² + mf²,
    using descent, (-m/p) = 1. Combined: (-1/p) = 1, p ≡ 1 mod 4.
-/
lemma p_mod4_eq1_of_dvd_v_not_dvd_m (p : ℕ) (q : ℤ) (b h x y v R m : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -m)
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : ¬ Even (padicValInt p v))
    (hpm : ¬ (p : ℤ) ∣ m) :
    p % 4 = 1 := by
  -- From R² + 2v = m, (m/p) = 1.
  -- From 4qv = e² + mf², using descent, (-m/p) = 1.
  -- Combining these: (-1/p) = 1, p ≡ 1 mod 4
  have h_jacobi_m : jacobiSym m p = 1 := by
    have hm_mod : (R ^ 2 : ℤ) ≡ m [ZMOD p] := by
      norm_num [ ← hRv, Int.modEq_iff_dvd ];
      refine' dvd_mul_of_dvd_right _ _;
      contrapose! hpv; simp_all +decide [ padicValInt.eq_zero_of_not_dvd ] ;
    haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, jacobiSym ];
    simp +decide [ Nat.primeFactorsList_prime hp ];
    haveI := Fact.mk hp; rw [ legendreSym.eq_one_iff ] ; aesop;
    rwa [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] at hpm
  have h_jacobi_neg_m : jacobiSym (-m) p = 1 := by
    by_cases hpq : ( p : ℤ ) ∣ q <;> simp_all +decide [ padicValInt.mul ];
    · -- Since $p \mid q$, we have $b^2 \equiv -m \pmod{p}$.
      have hb_sq_mod_p : b ^ 2 ≡ -m [ZMOD p] := by
        exact Int.modEq_iff_dvd.mpr ⟨ -4 * h * hpq.choose, by linear_combination -hbqm - 4 * h * hpq.choose_spec ⟩;
      haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, jacobiSym ] ;
      simp_all +decide [ Nat.primeFactorsList_prime hp ];
      rw [ legendreSym.eq_one_iff ] at *;
      · exact ⟨ b, by simpa [ sq ] using hb_sq_mod_p.symm ⟩;
      · rwa [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] at hpm;
      · simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
    · -- Since p ∤ q, we have padicValInt p (4qv) = padicValInt p v.
      have h_jacobi_neg_m_odd : ¬Even (padicValInt p ((2 * q * x + b * y) ^ 2 + m * y ^ 2)) := by
        have h_jacobi_neg_m_odd : padicValInt p (4 * q * v) = padicValInt p v := by
          haveI := Fact.mk hp; rw [ padicValInt.mul, padicValInt.mul ] <;> norm_num;
          · exact ⟨ Or.inr <| mod_cast fun h => hp_odd <| by have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> trivial, Or.inr <| Or.inr hpq ⟩;
          · aesop;
          · aesop_cat;
          · aesop;
        grind;
      apply jacobi_neg_d_of_odd_padicVal p (2 * q * x + b * y) m y hp hp_odd hpm h_jacobi_neg_m_odd
  have h_jacobi_neg_1 : jacobiSym (-1) p = 1 := by
    have h_mul : jacobiSym (-m) p = jacobiSym (-1) p * jacobiSym m p := by
      simpa [neg_mul] using (jacobiSym.mul_left (-1) m p)
    rw [h_mul, h_jacobi_m] at h_jacobi_neg_m
    simpa using h_jacobi_neg_m
  rw [ jacobiSym.at_neg_one ] at h_jacobi_neg_1;
  · rw [ ZMod.χ₄_nat_mod_four ] at h_jacobi_neg_1; have := Nat.mod_lt p zero_lt_four; interval_cases p % 4 <;> trivial;
  · exact hp.odd_of_ne_two hp_odd
/-- If p | v and p | m, with m squarefree, R² + 2v = m, and
    (-2q/p) = 1, then p ≡ 1 (mod 4) -/
lemma p_mod4_of_dvd_v_dvd_m (p : ℕ) (q : ℕ) (b h x y : ℤ) (R v : ℤ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3)
    (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m)
    (hjac : jacobiSym (-2 * q) p = 1) :
    False := by
  -- Since $p \mid m$ and $p \mid v$, we have $p \mid R$ and $p \mid (2qx + by)$.
  have hp_R : (p : ℤ) ∣ R := by
    exact Int.Prime.dvd_pow' hp <| by rw [← Int.dvd_add_left (dvd_mul_of_dvd_right hpv _)] ; exact hRv.symm ▸ Int.natCast_dvd_natCast.mpr hpm;
  have hp_2qx_by : (p : ℤ) ∣ (2 * q * x + b * y) := by
    have hp_2qx_by : (p : ℤ) ∣ ((2 * q * x + b * y) ^ 2 + m * y ^ 2) := by
      convert hpv.mul_left (4 * q) using 1 ; rw [hv] ; linear_combination' hbqm * y ^ 2;
    haveI := Fact.mk hp; simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd] ;
    obtain ⟨k, hk⟩ := hpm; simp_all +decide [← ZMod.natCast_eq_zero_iff] ;
  have h_y_sq_mod_p : y ^ 2 ≡ 2 * q [ZMOD p] := by
    have h_div_p : (m / p : ℤ) * y ^ 2 ≡ (m / p : ℤ) * (2 * q) [ZMOD p] := by
      have h_div_p : (4 * q * v : ℤ) ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
        obtain ⟨k, hk⟩ := hpv; simp_all +decide [Int.modEq_iff_dvd] ;
        obtain ⟨a, ha⟩ := hp_R; obtain ⟨b, hb⟩ := hp_2qx_by; simp_all +decide [← eq_sub_iff_add_eq', ← mul_assoc] ;
        exact ⟨a ^ 2 * 2 * q, by nlinarith⟩;
      have h_div_p : (4 * q * v : ℤ) ≡ (2 * q * x + b * y) ^ 2 + m * y ^ 2 [ZMOD p ^ 2] := by
        exact Int.modEq_of_dvd ⟨0, by rw [hv] ; linear_combination' hbqm * y ^ 2⟩;
      have h_div_p : (m : ℤ) * y ^ 2 ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
        simp_all +decide [Int.ModEq];
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at * ; aesop;
      rw [Int.modEq_iff_dvd] at *;
      obtain ⟨k, hk⟩ := h_div_p; use k; nlinarith [hp.two_le, Int.ediv_mul_cancel (show (p : ℤ) ∣ m from mod_cast hpm)] ;
    haveI := Fact.mk hp; simp_all +decide [← ZMod.intCast_eq_intCast_iff] ;
    cases h_div_p <;> simp_all +decide [ZMod.intCast_zmod_eq_zero_iff_dvd];
    norm_cast at *; simp_all +decide [Nat.squarefree_iff_prime_squarefree] ;
  have h_jacobi_2q_p : jacobiSym (2 * q) p = 1 := by
    haveI := Fact.mk hp; simp_all +decide [← ZMod.intCast_eq_intCast_iff, jacobiSym] ;
    simp_all +decide [Nat.primeFactorsList_prime hp];
    rw [legendreSym.eq_one_iff];
    · exact ⟨y, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using h_y_sq_mod_p.symm⟩;
    · intro H; simp_all +decide [legendreSym] ;
  haveI := Fact.mk hp; simp_all +decide [jacobiSym.mul_left, ← ZMod.intCast_eq_intCast_iff] ;
  rw [jacobiSym.neg] at hjac;
  · rw [ZMod.χ₄_nat_mod_four] at hjac ; simp_all +decide [jacobiSym.mul_left];
  · exact hp.odd_of_ne_two <| by aesop_cat
/-! ## Core valuation lemma: combining both cases -/
/-
The core step: every prime p ≡ 3 (mod 4) that is a prime factor of 2*v
has even p-adic valuation of 2*v. This means 2v is a sum of two squares.
-/
lemma even_padicVal_of_mod4_eq3 (p : ℕ) (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3)
    (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → jacobiSym (-2 * ↑q) ↑p' = 1) :
    Even (padicValNat p (2 * v)) := by
  by_cases hp2 : p = 2;
  · aesop;
  · -- Since $p$ is a prime factor of $2v$, we have $p \mid v$.
    by_cases hpv : (p : ℤ) ∣ v;
    · by_cases hpm : (p : ℕ) ∣ m;
      · have := p_mod4_of_dvd_v_dvd_m p q b h x y R v m hp hp3 hm_sq hv_def hbqm hRv hpv hpm ( hjac p hpm hp ) ; aesop;
      · have h_contradiction : ¬Even (padicValInt p v) → False := by
          intro h_odd;
          have := p_mod4_eq1_of_dvd_v_not_dvd_m p q b h x y v R m hp hp2 hv_def hbqm hRv (by
          exact h_odd) (by
          exact_mod_cast hpm);
          cases this.symm.trans hp3;
        simp_all +decide [ padicValNat.mul, hv_pos.ne' ];
        simp_all +decide [ padicValNat.eq_zero_of_not_dvd, ← hv_def ];
        rw [ padicValNat.eq_zero_of_not_dvd ] <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
    · rw [ padicValNat.eq_zero_of_not_dvd ] <;> norm_num;
      exact fun h => hpv <| Int.natCast_dvd_natCast.mpr <| hp.dvd_mul.mp h |> Or.resolve_left <| by intro t; have := Nat.le_of_dvd ( by positivity ) t; interval_cases p <;> trivial;
/-! ## Sum of two squares from padic valuation -/
/-- 2v is a sum of two squares -/
lemma two_v_sum_two_squares (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) :
    ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro p hp hp3
  exact even_padicVal_of_mod4_eq3 p q b h x y R v m
    hp hp3
    hm_sq hm_pos hq_prime hq_mod hv_pos hv_def hbqm hRv hjac
/-! ## Assembly: from R² + 2v = m to sum of three squares -/
/-
From R² + 2v = m and 2v = a² + b², we get m = R² + a² + b²
-/
lemma sum_three_from_Rsq_two_v (R : ℤ) (v : ℕ) (m : ℕ)
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hab : ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2) :
    ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
  grind +qlia
/-! ## Setup: combine existing lemmas to get R and v -/
/-
Step 1: Find prime q with q ≡ 1 mod 4 and (-2q/p) = 1 for all p | m
-/
lemma exists_prime_q (m : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  -- Let's choose any prime $q$ such that $q \equiv 1 \pmod{4}$ and $\left(\frac{-2q}{p}\right) = 1$ for all prime factors $p$ of $m$.
  obtain ⟨q, hq_prime, hq_mod, hq_jacobi⟩ : ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p : ℕ, p ∣ m → Nat.Prime p → jacobiSym (-2 * q : ℤ) p = 1 := by
    have h_crt : ∃ a : ℕ, a % 4 = 1 ∧ ∀ p : ℕ, p ∣ m → Nat.Prime p → jacobiSym (-2 * a : ℤ) p = 1 := by
      -- For each prime divisor $p$ of $m$, choose an integer $a_p$ such that $a_p \equiv 1 \pmod{4}$ and $\left(\frac{-2a_p}{p}\right) = 1$.
      obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ → ℕ, (∀ p : ℕ, Nat.Prime p → p ∣ m → a_p p % 4 = 1 ∧ jacobiSym (-2 * a_p p : ℤ) p = 1) := by
        have h_crt : ∀ p : ℕ, Nat.Prime p → p ∣ m → ∃ a_p : ℕ, a_p % 4 = 1 ∧ jacobiSym (-2 * a_p : ℤ) p = 1 := by
          intro p hp hpm
          by_cases hp2 : p = 2;
          · exact absurd ( Nat.dvd_trans ( by norm_num [ hp2 ] : 2 ∣ p ) hpm ) ( by omega );
          · -- Since $p$ is odd, we can choose $a_p$ such that $a_p \equiv 1 \pmod{4}$ and $a_p \equiv -2^{-1} \pmod{p}$.
            obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, a_p % 4 = 1 ∧ a_p * 2 ≡ -1 [ZMOD p] := by
              have h_crt : ∃ a_p : ℤ, a_p ≡ 1 [ZMOD 4] ∧ a_p * 2 ≡ -1 [ZMOD p] := by
                have h_crt : ∃ a_p : ℤ, a_p ≡ 1 [ZMOD 4] ∧ a_p ≡ -1 * (2⁻¹ : ZMod p).val [ZMOD p] := by
                  have h_crt : Nat.gcd 4 p = 1 := by
                    exact Nat.Coprime.symm ( hp.coprime_iff_not_dvd.mpr fun h => hp2 <| by have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> trivial );
                  have := Nat.chineseRemainder h_crt;
                  obtain ⟨ k, hk₁, hk₂ ⟩ := this 1 ( Int.toNat ( -1 * ( 2⁻¹ : ZMod p ).val % p ) ) ; use k; simp_all +decide [ ← Int.natCast_modEq_iff ] ;
                  simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ];
                haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
                obtain ⟨ a_p, ha_p₁, ha_p₂ ⟩ := h_crt; use a_p; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
                rw [ inv_mul_cancel₀ ( show ( 2 : ZMod p ) ≠ 0 from by erw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two <| lt_of_le_of_ne hp.two_le <| Ne.symm hp2 ) ];
              obtain ⟨ a_p, ha_p₁, ha_p₂ ⟩ := h_crt;
              use Int.toNat ( a_p % ( 4 * p ) );
              rw [ ← Int.natCast_inj ] ; simp_all +decide [ Int.ModEq ];
              norm_num [ Int.mul_emod, Int.emod_nonneg _ ( by linarith [ hp.pos ] : ( 4 * p : ℤ ) ≠ 0 ) ] at * ; aesop;
            use a_p;
            haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, jacobiSym ] ;
            simp_all +decide [ mul_comm, legendreSym ];
            norm_num [ ha_p, Nat.primeFactorsList_prime hp ];
        choose! a_p ha_p using h_crt;
        use a_p;
      -- By the Chinese Remainder Theorem, there exists an integer $a$ such that $a \equiv a_p \pmod{p}$ for all prime factors $p$ of $m$ and $a \equiv 1 \pmod{4}$.
      obtain ⟨a, ha⟩ : ∃ a : ℕ, (∀ p : ℕ, Nat.Prime p → p ∣ m → a ≡ a_p p [MOD p]) ∧ a ≡ 1 [MOD 4] := by
        -- Applying the Chinese Remainder Theorem.
        have h_crt : ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) → (∀ p ∈ I, p ∣ m) → ∃ a : ℕ, (∀ p ∈ I, a ≡ a_p p [MOD p]) ∧ a ≡ 1 [MOD 4] := by
          intros I hI_prime hI_div
          induction' I using Finset.induction with p I hI ih;
          · exists 1;
            norm_num;
          · obtain ⟨ a, ha₁, ha₂ ⟩ := ih ( fun q hq => hI_prime q ( Finset.mem_insert_of_mem hq ) ) ( fun q hq => hI_div q ( Finset.mem_insert_of_mem hq ) );
            -- We need to find an integer $x$ such that $x \equiv a \pmod{4 \prod_{q \in I} q}$ and $x \equiv a_p p \pmod{p}$.
            obtain ⟨ x, hx ⟩ : ∃ x : ℕ, x ≡ a [MOD 4 * ∏ q ∈ I, q] ∧ x ≡ a_p p [MOD p] := by
              have h_crt : Nat.gcd (4 * ∏ q ∈ I, q) p = 1 := by
                refine' Nat.Coprime.mul_left _ _;
                · rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.prime_mul_iff ];
                  · omega;
                  · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num;
                · exact Nat.Coprime.prod_left fun q hq => Nat.coprime_comm.mp <| hI_prime p ( Finset.mem_insert_self _ _ ) |> Nat.Prime.coprime_iff_not_dvd |>.2 fun h => hI <| by have := Nat.prime_dvd_prime_iff_eq ( hI_prime p ( Finset.mem_insert_self _ _ ) ) ( hI_prime q ( Finset.mem_insert_of_mem hq ) ) ; aesop;
              have := Nat.chineseRemainder h_crt;
              exact ⟨ _, this a ( a_p p ) |>.2 ⟩;
            use x;
            simp_all +decide [ Nat.ModEq ];
            exact ⟨ fun q hq => by rw [ ← Nat.mod_mod_of_dvd x ( show q ∣ 4 * ∏ q ∈ I, q from dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ hq ) _ ), hx.1, Nat.mod_mod_of_dvd _ ( show q ∣ 4 * ∏ q ∈ I, q from dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ hq ) _ ), ha₁ q hq ], by rw [ ← Nat.mod_mod_of_dvd x ( show 4 ∣ 4 * ∏ q ∈ I, q from dvd_mul_right _ _ ), hx.1, Nat.mod_mod_of_dvd _ ( show 4 ∣ 4 * ∏ q ∈ I, q from dvd_mul_right _ _ ), ha₂ ] ⟩;
        specialize h_crt (Nat.primeFactors m);
        aesop;
      refine' ⟨ a, ha.2, fun p hp hp' => _ ⟩;
      haveI := Fact.mk hp'; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, jacobiSym ] ;
      specialize ha_p p hp' hp ; simp_all +decide [ Nat.primeFactorsList_prime hp' ];
      haveI := Fact.mk hp'; simp_all +decide [ legendreSym ] ;
    obtain ⟨ a, ha₁, ha₂ ⟩ := h_crt;
    -- By Dirichlet's theorem on primes in arithmetic progressions, there exists a prime $q$ such that $q \equiv a \pmod{4m}$.
    obtain ⟨q, hq_prime, hq_mod⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ≡ a [MOD 4 * m] := by
      -- By Dirichlet's theorem, there are infinitely many primes in the arithmetic progression $a + k \cdot (4m)$ for $k \in \mathbb{N}$.
      have h_dirichlet : Set.Infinite {q : ℕ | Nat.Prime q ∧ q ≡ a [MOD 4 * m]} := by
        have h_dirichlet : Nat.Coprime a (4 * m) := by
          rw [ Nat.coprime_mul_iff_right ];
          refine' ⟨ Nat.Coprime.symm ( Nat.Coprime.gcd_eq_one <| Nat.Coprime.pow_left 2 <| Nat.prime_two.coprime_iff_not_dvd.mpr <| by omega ), Nat.coprime_of_dvd' _ ⟩;
          intro k hk hk₁ hk₂; specialize ha₂ k hk₂ hk; rw [ jacobiSym.mod_left ] at ha₂;
          simp_all +decide [ Int.emod_eq_zero_of_dvd, dvd_mul_of_dvd_right ];
          rw [ Int.emod_eq_zero_of_dvd <| dvd_neg.mpr <| dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr hk₁ ) _ ] at ha₂ ; rcases k with ( _ | _ | _ | k ) <;> norm_num [ jacobiSym ] at *;
        have := @Nat.setOf_prime_and_eq_mod_infinite;
        specialize @this ( 4 * m ) ?_ ( a : ZMod ( 4 * m ) ) ?_ <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        · exact ⟨ by aesop_cat ⟩;
        · exact (ZMod.isUnit_iff_coprime a (4 * m)).2 h_dirichlet;
      exact h_dirichlet.nonempty;
    refine' ⟨ q, hq_prime, _, _ ⟩;
    · exact hq_mod.of_dvd ( dvd_mul_right _ _ ) ▸ ha₁;
    · intro p hp hp_prime
      have h_cong : q ≡ a [MOD p] := by
        exact hq_mod.of_dvd <| dvd_mul_of_dvd_right hp _;
      haveI := Fact.mk hp_prime; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, jacobiSym ] ;
      specialize ha₂ p hp hp_prime ; simp_all +decide [ Nat.primeFactorsList_prime hp_prime ];
      simp_all +decide [ legendreSym ];
  use q
/-
Step 2: (-m/q) = 1
-/
lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    jacobiSym (-m) q = 1 := by
  -- By multiplicativity of the Jacobi symbol, we can write jacobiSym (-m/q) as jacobiSym (-1/q) * jacobiSym (m/q).
  have h_mul : jacobiSym (-m) q = jacobiSym (-1) q * jacobiSym m q := by
    rw [ ← jacobiSym.mul_left ] ; ring;
  -- By multiplicativity of the Jacobi symbol, we can write jacobiSym (-m/q) as jacobiSym (-1/q) * jacobiSym (m/q). Using the fact that jacobiSym (-2*q) m = 1, we get:
  have h_mul : jacobiSym (-2) m * jacobiSym q m = 1 := by
    rw [ ← jacobiSym.mul_left ];
    rw [ jacobiSym ];
    rw [ List.prod_eq_one ] ; intros ; simp_all +decide [ jacobiSym ];
    rcases ‹_› with ⟨ p, hp, rfl ⟩ ; specialize h_jacobi p hp.2.1 hp.1; simp_all +decide [ Nat.primeFactorsList_prime hp.1 ] ;
  -- Using the fact that jacobiSym (-2) m = 1, we get:
  have h_jacobi_neg2 : jacobiSym (-2) m = 1 := by
    rw [ jacobiSym.mod_right ];
    · norm_num [ hm_mod ];
    · exact Nat.odd_iff.mpr ( by omega );
  -- Using the fact that jacobiSym q m = 1, we get:
  have h_jacobi_qm : jacobiSym q m = jacobiSym m q := by
    rw [ jacobiSym.quadratic_reciprocity ];
    · norm_num [ Nat.even_div, hq_mod, hm_mod ];
    · exact hq_prime.odd_of_ne_two <| by aesop_cat;
    · exact Nat.odd_iff.mpr ( by omega );
  simp_all +decide [ jacobiSym.mod_right ];
  rw [ jacobiSym.mod_right ] ; norm_num [ hq_mod ];
  exact hq_prime.odd_of_ne_two <| by aesop_cat
/-
Step 3: Find b, h with b odd and b² - 4qh = -m
-/
lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b % 2 = 1 ∧ b ^ 2 - 4 * q * h = -m := by
  -- Since jacobiSym(-m, q) = 1, there exists an odd integer b₀ such that b₀² ≡ -m (mod q).
  obtain ⟨b₀, hb₀_mod⟩ : ∃ b₀ : ℤ, b₀ % 2 = 1 ∧ b₀ ^ 2 ≡ -m [ZMOD q] := by
    obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℤ, b₀ ^ 2 ≡ -m [ZMOD q] := by
      rw [ jacobiSym ] at h_jacobi;
      haveI := Fact.mk hq_prime; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, Nat.primeFactorsList_prime hq_prime ] ;
      rw [ legendreSym.eq_one_iff ] at h_jacobi;
      · obtain ⟨ x, hx ⟩ := h_jacobi; use x.val; simpa [ sq, ← ZMod.intCast_eq_intCast_iff ] using hx.symm;
      · rw [ legendreSym ] at h_jacobi ; aesop;
    by_cases hb₀_odd : b₀ % 2 = 1;
    · use b₀;
    · refine' ⟨ b₀ + q, _, _ ⟩ <;> simp_all +decide [ Int.ModEq, ← even_iff_two_dvd, parity_simps ];
      · norm_num [ Int.even_iff.mp hb₀_odd, Int.add_emod, show ( q : ℤ ) % 2 = 1 from mod_cast hq_prime.eq_two_or_odd.resolve_left ( by aesop_cat ) ];
      · simpa [ sq, Int.add_emod, Int.mul_emod ] using hb₀;
  obtain ⟨ k, hk ⟩ := hb₀_mod.2.symm.dvd;
  -- Since $b₀$ is odd and $m \equiv 3 \pmod{8}$, we have $b₀^2 + m \equiv 1 + 3 \equiv 4 \equiv 0 \pmod{4}$.
  have h_div4 : 4 ∣ (k : ℤ) := by
    rw [ Int.dvd_iff_emod_eq_zero ] ; replace hk := congr_arg ( · % 4 ) hk ; rcases Int.even_or_odd' b₀ with ⟨ b₀, rfl | rfl ⟩ <;> rcases Int.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] at *;
    · norm_cast at hk; rw [ ← Nat.mod_mod_of_dvd m ( by decide : 4 ∣ 8 ), hm_mod ] at hk; have := Int.emod_nonneg k four_pos.ne'; have := Int.emod_lt_of_pos k four_pos; interval_cases k % 4 <;> simp_all +decide ;
    · norm_cast at *; rw [ ← Nat.mod_mod_of_dvd m ( by decide : 4 ∣ 8 ), hm_mod ] at hk; ( rw [ ← Nat.mod_mod_of_dvd q ( by decide : 4 ∣ 4 ), hq_mod ] at hk; have := Int.emod_nonneg k four_pos.ne'; have := Int.emod_lt_of_pos k four_pos; interval_cases k % 4 <;> trivial; );
  obtain ⟨ h, rfl ⟩ := h_div4; exact ⟨ b₀, h, hb₀_mod.1, by linarith ⟩ ;
/-
Step 4: Find t with 2qt² ≡ -1 mod m
-/
lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, t ^ 2 * 2 * q ≡ -1 [ZMOD m] := by
  rcases m.eq_zero_or_pos with ( rfl | hm_pos ) <;> norm_cast;
  -- For each prime p | m, find s_p with s_p² ≡ -2q mod p, then t_p = s_p^{-1} mod p satisfies 2q·t_p² ≡ -1 mod p.
  have h_crt : ∀ p ∈ Nat.primeFactors m, ∃ t_p : ℤ, t_p ^ 2 * 2 * q ≡ -1 [ZMOD p] := by
    intro p hp
    have h_jacobi_p : jacobiSym (-2 * q) p = 1 := h_jacobi p (Nat.dvd_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hp);
    rw [ jacobiSym ] at h_jacobi_p;
    norm_num [ Nat.primeFactorsList_prime ( Nat.prime_of_mem_primeFactors hp ) ] at h_jacobi_p;
    haveI := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, legendreSym ] ;
    rw [ quadraticCharFun ] at h_jacobi_p;
    split_ifs at h_jacobi_p ; simp_all +decide [ isSquare_iff_exists_sq ];
    obtain ⟨ x, hx ⟩ := ‹IsSquare ( - ( 2 * ( q : ZMod p ) ) ) ›; use x⁻¹.val; simp_all +decide [ mul_assoc, sq ] ;
    grind;
  choose! t ht using h_crt;
  -- By the Chinese Remainder Theorem, there exists an integer $t$ such that $t \equiv t_p \pmod{p}$ for each prime $p \mid m$.
  obtain ⟨t_crt, ht_crt⟩ : ∃ t_crt : ℤ, ∀ p ∈ Nat.primeFactors m, t_crt ≡ t p [ZMOD p] := by
    have h_crt : ∀ p ∈ Nat.primeFactors m, ∃ x : ℤ, x ≡ t p [ZMOD p] ∧ ∀ q ∈ Nat.primeFactors m, q ≠ p → x ≡ 0 [ZMOD q] := by
      -- For each prime $p \mid m$, let $y_p$ be the multiplicative inverse of $\prod_{q \mid m, q \neq p} q$ modulo $p$.
      intro p hp
      obtain ⟨y_p, hy_p⟩ : ∃ y_p : ℤ, y_p * (∏ q ∈ Nat.primeFactors m \ {p}, q) ≡ 1 [ZMOD p] := by
        have h_coprime : Nat.gcd p (∏ q ∈ Nat.primeFactors m \ {p}, q) = 1 := by
          exact Nat.Coprime.prod_right fun q hq => by have := Nat.coprime_primes ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors ( Finset.mem_sdiff.mp hq |>.1 ) ) ; aesop;
        have := Nat.gcd_eq_gcd_ab p ( ∏ q ∈ m.primeFactors \ { p }, q );
        exact ⟨ Nat.gcdB p ( ∏ q ∈ m.primeFactors \ { p }, q ), Int.modEq_iff_dvd.mpr ⟨ Nat.gcdA p ( ∏ q ∈ m.primeFactors \ { p }, q ), by linarith ⟩ ⟩;
      use y_p * (∏ q ∈ Nat.primeFactors m \ {p}, q) * t p;
      exact ⟨ by simpa using hy_p.mul_right _, fun q hq hqp => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( mod_cast Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
    choose! x hx₁ hx₂ using h_crt;
    use ∑ p ∈ m.primeFactors, x p;
    intro p hp; simp_all +decide only [Int.ModEq];
    simp +zetaDelta at *;
    rw [ Finset.sum_int_mod, Finset.sum_eq_single p ] <;> aesop;
  -- Therefore, $t_crt^2 * 2 * q \equiv -1 \pmod{p}$ for each prime $p \mid m$.
  have ht_crt_mod : ∀ p ∈ Nat.primeFactors m, t_crt ^ 2 * 2 * q ≡ -1 [ZMOD p] := by
    exact fun p hp => Eq.trans ( Int.ModEq.mul ( Int.ModEq.mul ( ht_crt p hp |> Int.ModEq.pow _ ) rfl ) rfl ) ( ht p hp );
  use t_crt;
  simp_all +decide [ Int.modEq_iff_dvd ];
  -- Since $m$ is squarefree, the product of its prime factors is $m$.
  have h_prod_prime_factors : (∏ p ∈ Nat.primeFactors m, (p : ℤ)) = m := by
    rw [ ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm_sq ];
  exact h_prod_prime_factors ▸ Finset.prod_dvd_of_coprime ( fun p hp q hq hpq => by have := Nat.coprime_primes ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ; aesop ) ( fun p hp => ht_crt_mod p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) hm_pos.ne' )
/-
The quadratic form R²+S²+T² = R² + 2(qx²+bxy+hy²)
-/
lemma rst_expand (m q : ℕ) (t b h x y z : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    (2 * t * q * x + t * b * y + m * z) ^ 2 +
      (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
      (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 =
    (2 * t * q * x + t * b * y + m * z) ^ 2 +
      2 * ((q : ℝ) * x ^ 2 + (b : ℝ) * x * y + (h : ℝ) * y ^ 2) := by
  field_simp;
  norm_num [ mul_pow ];
  rw [ show ( m : ℝ ) = - ( b ^ 2 - 4 * q * h ) by exact mod_cast hbqm ▸ by ring ] ; ring
/-
R² + 2v ≡ 0 mod m
-/
lemma rst_mod_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : t ^ 2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    (2 * t * q * x + t * b * y + m * z) ^ 2 +
      2 * (q * x ^ 2 + b * x * y + h * y ^ 2) ≡ 0 [ZMOD m] := by
  simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, add_assoc ];
  replace hbqm := congr_arg ( ( ↑ ) : ℤ → ZMod m ) hbqm;
  simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
  grind
/-
If R² + S² + T² = 0 then x = y = z = 0
-/
lemma xyz_zero_of_sum_sq_zero (m q : ℕ) (t b x y z : ℤ) (hm : 0 < m) (hq : 0 < q)
    (h : (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
        (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
        (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  -- From $T^2 = 0$, we get $y = 0$.
  have hy : y = 0 := by
    contrapose! h; positivity;
  simp_all +decide [ add_eq_zero_iff_of_nonneg, sq_nonneg ];
  cases h.2 <;> simp_all +decide [ ne_of_gt ]
/-
By Minkowski, there exist nonzero integers x,y,z with R²+S²+T² < 2m
-/
lemma exists_lattice_point (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
      (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 < 2 * m := by
  -- Define the set S = {v : Fin 3 → ℝ | (2tq·v0 + tb·v1 + m·v2)² + (√(2q)·v0 + b/√(2q)·v1)² + (√m/√(2q)·v1)² < 2m}.
  let S : Set (Fin 3 → ℝ) := {v : Fin 3 → ℝ |
    ((2 * t * q * v 0 + t * b * v 1 + m * v 2) ^ 2 +
      ((Real.sqrt (2 * q)) * (v 0) + (b : ℝ) / ((Real.sqrt (2 * q))) * (v 1)) ^ 2 +
      ((Real.sqrt m) / (Real.sqrt (2 * q)) * (v 1)) ^ 2) < 2 * m};
  -- We need to show that the volume of $S$ is greater than $8$.
  have h_volume : MeasureTheory.volume S > 8 := by
    -- The volume of the ellipsoid is given by $\frac{4\pi}{3} \cdot \frac{(2m)^{3/2}}{|det M|}$.
    have h_volume_formula : MeasureTheory.volume S = ENNReal.ofReal ((4 * Real.pi / 3) * (2 * m) ^ (3 / 2 : ℝ) / abs (m * Real.sqrt m)) := by
      -- The volume of the ellipsoid is given by $\frac{4\pi}{3} \cdot \frac{(2m)^{3/2}}{|det M|}$, where $M$ is the matrix representing the quadratic form.
      have h_volume_formula : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), M.det ≠ 0 → MeasureTheory.volume {v : Fin 3 → ℝ | (M.mulVec v) 0 ^ 2 + (M.mulVec v) 1 ^ 2 + (M.mulVec v) 2 ^ 2 < 2 * m} = ENNReal.ofReal ((4 * Real.pi / 3) * (2 * m) ^ (3 / 2 : ℝ) / abs (Matrix.det M)) := by
        intro M hM_det
        have h_volume_formula : MeasureTheory.volume {v : Fin 3 → ℝ | (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 < 2 * m} = ENNReal.ofReal ((4 * Real.pi / 3) * (2 * m) ^ (3 / 2 : ℝ)) := by
          have := @MeasureTheory.volume_sum_rpow_lt;
          convert @this ( Fin 3 ) _ _ 2 ( by norm_num ) ( Real.sqrt ( 2 * m ) ) using 1 <;> norm_num [ Fin.sum_univ_three ];
          · norm_num [ ← Real.sqrt_eq_rpow, Real.sqrt_lt' ( by positivity : 0 < Real.sqrt 2 * Real.sqrt m ) ];
            norm_num [ mul_pow, hm.le ];
          · rw [ show ( 3 / 2 : ℝ ) = 1 / 2 + 1 by norm_num, show ( 5 / 2 : ℝ ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one, Real.Gamma_add_one ] <;> norm_num;
            rw [ show ( 3 / 2 : ℝ ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one ( by norm_num ), Real.Gamma_one_half_eq ] ; ring ; norm_num [ ← ENNReal.ofReal_mul, Real.pi_pos.le ];
            rw [ show ( m * 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = ( m * 2 : ℝ ) * Real.sqrt ( m * 2 ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; norm_num [ pow_three, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.le, ne_of_gt Real.pi_pos ] ; ring;
            norm_num [ pow_three, mul_assoc, mul_comm, mul_left_comm, ENNReal.ofReal_mul, Real.sqrt_nonneg ];
            norm_num [ ← mul_assoc, ← ENNReal.ofReal_mul, Real.sqrt_nonneg ] ; ring;
            norm_num [ mul_assoc, mul_comm, mul_left_comm, ENNReal.ofReal_mul, Real.sqrt_nonneg ];
        have := @MeasureTheory.Measure.addHaar_preimage_linearMap;
        convert this MeasureTheory.volume ( show LinearMap.det ( Matrix.toLin' M ) ≠ 0 from by simpa [ Matrix.det_apply' ] using hM_det ) { v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m } using 1;
        rw [ h_volume_formula, ENNReal.ofReal_div_of_pos ] <;> norm_num [ hM_det ];
        rw [ ENNReal.div_eq_inv_mul ];
      convert h_volume_formula ( Matrix.of fun i j => if i = 0 then if j = 0 then 2 * t * q else if j = 1 then t * b else m else if i = 1 then if j = 0 then Real.sqrt ( 2 * q ) else if j = 1 then b / Real.sqrt ( 2 * q ) else 0 else if i = 2 then if j = 0 then 0 else if j = 1 then Real.sqrt m / Real.sqrt ( 2 * q ) else 0 else 0 ) _ using 1 <;> norm_num [ Fin.sum_univ_three, Matrix.det_fin_three ];
        · apply congrArg MeasureTheory.volume
          ext v
          constructor <;> intro hv <;>
            simpa [S, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
              Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) (q : ℝ)] using hv
      · simp +decide [ Fin.ext_iff ] ; ring;
        norm_num [ abs_of_nonneg, Real.sqrt_nonneg, mul_assoc, mul_comm, mul_left_comm, hm.ne', hq.ne' ];
      · simp +decide [ Fin.ext_iff ] ; ring_nf ; norm_num [ hm.ne', hq.ne' ];
    rw [ h_volume_formula, gt_iff_lt, ENNReal.lt_ofReal_iff_toReal_lt ] <;> norm_num;
    rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), lt_div_iff₀ ] <;> try positivity;
    rw [ show ( 2 * m : ℝ ) ^ ( 3 / 2 : ℝ ) = ( 2 * m : ℝ ) * Real.sqrt ( 2 * m ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num [ hm.ne', hq.ne' ];
    nlinarith only [ show 0 < ( m : ℝ ) * Real.sqrt m by positivity, show 0 < ( m : ℝ ) * Real.sqrt m * Real.sqrt 2 by positivity, Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_lt_mul_of_pos_left Real.pi_gt_three <| show 0 < ( m : ℝ ) * Real.sqrt m by positivity ];
  have h_symm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp [S] at hx ⊢
    nlinarith
  have h_conv : Convex ℝ S := by
    refine' convex_iff_forall_pos.mpr _;
    intros x hx y hy a b ha hb hab
    simp [S] at hx hy ⊢;
    rw [ ← eq_sub_iff_add_eq' ] at hab;
    subst hab;
    nlinarith [ mul_pos ha hb, sq_nonneg ( ( 2 * t * q * x 0 + t * b * x 1 + m * x 2 ) - ( 2 * t * q * y 0 + t * b * y 1 + m * y 2 ) ), sq_nonneg ( ( Real.sqrt 2 * Real.sqrt q * x 0 + b / ( Real.sqrt 2 * Real.sqrt q ) * x 1 ) - ( Real.sqrt 2 * Real.sqrt q * y 0 + b / ( Real.sqrt 2 * Real.sqrt q ) * y 1 ) ), sq_nonneg ( ( Real.sqrt m / ( Real.sqrt 2 * Real.sqrt q ) * x 1 ) - ( Real.sqrt m / ( Real.sqrt 2 * Real.sqrt q ) * y 1 ) ) ];
  have h_pow : (2 : ENNReal) ^ 3 < MeasureTheory.volume S := by
    norm_num
    simpa [gt_iff_lt] using h_volume
  let S' : Set (EuclideanSpace ℝ (Fin 3)) := S
  have h_symm' : ∀ x ∈ S', -x ∈ S' := by
    simpa [S'] using h_symm
  have h_conv' : Convex ℝ S' := by
    simpa [S'] using h_conv
  have h_pow' : (2 : ENNReal) ^ 3 < MeasureTheory.volume S' := by
    simp [S']
    exact h_pow
  obtain ⟨w, hw_ne, hw_mem, hw_int⟩ :=
    classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (n := 3) (s := S') h_symm' h_conv' h_pow'
  obtain ⟨x, hx⟩ := hw_int 0
  obtain ⟨y, hy⟩ := hw_int 1
  obtain ⟨z, hz⟩ := hw_int 2
  refine ⟨x, y, z, ?_, ?_⟩
  · intro hxyz
    have hx0 : x = 0 := by simpa using congrArg Prod.fst hxyz
    have hyz : (y, z) = (0, 0) := by simpa using congrArg Prod.snd hxyz
    have hy0 : y = 0 := by simpa using congrArg Prod.fst hyz
    have hz0 : z = 0 := by simpa using congrArg Prod.snd hyz
    apply hw_ne
    ext i
    fin_cases i
    · simpa [hx0] using hx.symm
    · simpa [hy0] using hy.symm
    · simpa [hz0] using hz.symm
  · simpa [S', S, hx, hy, hz] using hw_mem
/-
Step 5 & 6: Use Minkowski's theorem to get R, v with R² + 2v = m, v > 0
-/
lemma exists_Rv_from_Minkowski (m q : ℕ) (t b h : ℤ) (hm : 0 < m) (hq : 0 < q)
    (hqt : t ^ 2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    ∃ (x y : ℤ) (R : ℤ) (v : ℕ),
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  have h_exists : ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 + (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 + (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 < 2 * m := by
    exact exists_lattice_point m q t b hm hq
  obtain ⟨ x, y, z, hne, hlt ⟩ := h_exists;
  -- From the inequality $R^2 + 2v < 2m$, we know that $R^2 + 2v$ must be either $0$ or $m$ since $m$ is a positive integer.
  have h_cases : (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 + 2 * (q * x ^ 2 + b * x * y + h * y ^ 2) = 0 ∨ (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 + 2 * (q * x ^ 2 + b * x * y + h * y ^ 2) = m := by
    have h_cases : (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 + 2 * (q * x ^ 2 + b * x * y + h * y ^ 2) ≡ 0 [ZMOD m] := by
      exact rst_mod_zero m q t b h x y z hqt hbqm
    have h_cases : (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 + 2 * (q * x ^ 2 + b * x * y + h * y ^ 2) < 2 * m := by
      have h_expand : (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 + (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 + (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 = (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 + 2 * (q * x ^ 2 + b * x * y + h * y ^ 2) := by
        convert rst_expand m q t b h x y z ( by positivity ) ( mod_cast hbqm ) using 1;
        norm_num;
      exact_mod_cast h_expand ▸ hlt;
    obtain ⟨ k, hk ⟩ := Int.modEq_zero_iff_dvd.mp ‹_›;
    rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> first | left; nlinarith | skip;
    · nlinarith [ show ( q : ℤ ) * x ^ 2 + b * x * y + h * y ^ 2 ≥ 0 by nlinarith [ sq_nonneg ( 2 * q * x + b * y ) ] ];
    · rcases lt_trichotomy k 1 with hk'' | rfl | hk'' <;> first | left; nlinarith | right; nlinarith;
  cases' h_cases with h_case1 h_case2;
  · -- If $R^2 + 2v = 0$, then $x = y = z = 0$, contradicting $(x, y, z) \neq (0, 0, 0)$.
    have h_contra : x = 0 ∧ y = 0 ∧ z = 0 := by
      apply xyz_zero_of_sum_sq_zero m q t b x y z hm hq;
      convert congr_arg ( ( ↑ ) : ℤ → ℝ ) h_case1 using 1 ; norm_num;
      · convert rst_expand m q t b h x y z hq hbqm using 1;
      · norm_num;
    aesop;
  · refine' ⟨ x, y, 2 * t * q * x + t * b * y + m * z, Int.toNat ( q * x ^ 2 + b * x * y + h * y ^ 2 ), _, _, _ ⟩ <;> norm_num;
    · nlinarith [ sq_nonneg ( 2 * q * x + b * y ) ];
    · rw [ max_eq_left ];
      · convert h_case2 using 1;
      · nlinarith [ sq_nonneg ( 2 * q * x + b * y ) ];
    · contrapose! hne;
      have hxy_zero : x = 0 ∧ y = 0 := by
        have hxy_zero : q * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
          nlinarith [ sq_nonneg ( 2 * q * x + b * y ) ];
        by_cases hy : y = 0;
        · aesop;
        · nlinarith [ sq_nonneg ( 2 * q * x + b * y ), mul_self_pos.mpr hy ];
      simp_all +decide [ ne_of_gt ];
      rcases m with ( _ | _ | m ) <;> norm_num at *;
      · exact absurd ( congr_arg ( · % 4 ) hbqm ) ( by norm_num [ sq, Int.add_emod, Int.sub_emod, Int.mul_emod ] ; have := Int.emod_nonneg b four_pos.ne'; have := Int.emod_lt_of_pos b four_pos; interval_cases b % 4 <;> trivial );
      · nlinarith [ show z ^ 2 * ( m + 1 + 1 ) = 1 by nlinarith ]
/-- There exist q, b, h, t, x, y, z yielding R² + 2v = m with v > 0 -/
lemma exists_R_v_of_mod8_eq3 (m : ℕ) (hm : Squarefree m) (hm_pos : 0 < m) (hmod : m % 8 = 3) :
    ∃ (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ),
      Nat.Prime q ∧ q % 4 = 1 ∧
      (∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) ∧
      b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ) ∧
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨q, hq_prime, hq_mod, hjac⟩ := exists_prime_q m hm hmod
  obtain ⟨b, h, _, hbqm⟩ := exists_b_h m q hmod hq_prime hq_mod (jacobi_neg_m_q m q hmod hq_prime hq_mod hjac)
  obtain ⟨t, hqt⟩ := exists_t m q hm hmod hq_prime hjac
  obtain ⟨x, y, R, v, hv_def, hRv, hv_pos⟩ := exists_Rv_from_Minkowski m q t b h hm_pos (hq_prime.pos) hqt hbqm
  exact ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩
/-- Main theorem: m ≡ 3 (mod 8) squarefree ⟹ sum of three integer squares -/
theorem sum_three_squares_of_mod8_eq3 (m : ℕ) (hm : Squarefree m)
    (hm_pos : 0 < m) (hmod : m % 8 = 3) :
    ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩ :=
    exists_R_v_of_mod8_eq3 m hm hm_pos hmod
  have h2v := two_v_sum_two_squares q b h x y R v m hm hm_pos hq_prime hq_mod hv_pos hv_def hbqm hRv hjac
  exact sum_three_from_Rsq_two_v R v m hRv h2v
/-- The final theorem -/
theorem blueprint_case_mod8_eq3 (m : ℕ) (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hm_mod : m % 8 = 3) : IsSumOfThreeSquares m := by
  obtain ⟨a, b, c, habc⟩ := sum_three_squares_of_mod8_eq3 m hm_sq hm_pos hm_mod
  refine ⟨a.natAbs, b.natAbs, c.natAbs, ?_⟩
  apply Int.ofNat.inj
  calc
    ((a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 : ℕ) : ℤ)
        = a ^ 2 + b ^ 2 + c ^ 2 := by
          norm_num [Int.natCast_natAbs, sq_abs]
    _ = (m : ℤ) := by simpa using habc.symm
end
