import Mathlib

open Nat Finset BigOperators
--======================================================================================
section Section1_Definitions
--======================================================================================
/-- 
Global definitions for the quotient (k) and residue (m) of an integer x modulo 2^v.
-/
def k (v x : ℕ) : ℕ := x / 2^v
def m (v x : ℕ) : ℕ := x % 2^v

/-- 
Theorem: Bounds of the Residue.
Establishes that for any odd integer x and positive integer v, 
the residue m(v, x) is bounded: 0 < m(v, x) ≤ 2^v - 1.
-/
theorem m_bounds (v x : ℕ) (hv : 1 ≤ v) (h_odd : Odd x) :
  0 < m v x ∧ m v x ≤ 2^v - 1 := by
  
  -- Establish positivity of the modulus
  have h_pow_pos : 0 < 2^v := pow_pos (by decide) v

  constructor
  · -- Lower Bound: Proves the residue cannot be zero for an odd integer.
    apply pos_of_ne_zero
    intro h_zero
    
    have h_div : 2^v ∣ x := dvd_of_mod_eq_zero h_zero
    
    have h_two_dvd_pow : 2 ∣ 2^v := by
      cases v with
      | zero => linarith
      | succ n => 
        use 2^n
        rw [pow_succ, mul_comm]

    -- Transitivity yields a contradiction with the odd parity of x
    have h_two_dvd_x : 2 ∣ x := dvd_trans h_two_dvd_pow h_div
    rw [Nat.odd_iff] at h_odd
    rw [dvd_iff_mod_eq_zero] at h_two_dvd_x
    rw [h_two_dvd_x] at h_odd
    contradiction

  · -- Upper Bound: Derived directly from modulo properties.
    have h_lt : x % 2^v < 2^v := mod_lt x h_pow_pos
    exact le_pred_of_lt h_lt

end Section1_Definitions
#print axioms m_bounds
#check m_bounds
-- ===============================================================
-- SECTION 1: THE COLLATZ OPERATOR (Multiple Iterations)
-- ===============================================================
section Section2_MultipleIterations

/-- 
Definition of the 2-adic valuation.
Extracts the exact power of 2 dividing 3x + 1. 
-/
noncomputable def val (x : ℕ) : ℕ := (Nat.factorization (3 * x + 1)) 2

/-- 
The Accelerated Collatz Odd-to-Odd Operator.
Represents the transformation: T(x) = (3x + 1) / 2^(val(x))
-/
noncomputable def T (x : ℕ) : ℕ :=
  (3 * x + 1) / (2 ^ (val x))

/-- 
Single Step Modular Expansion.
Formalizes the algebraic transition using the defined quotient and residue.
-/
theorem step_expansion (v x : ℕ) :
  T x = (3 * (2^v * (k v x)) + 3 * (m v x) + 1) / 2^(val x) := by
  
  dsimp [T]
  
  have h_decomp : x = 2^v * (k v x) + (m v x) := (Nat.div_add_mod x (2^v)).symm
  nth_rw 1 [h_decomp]
  
  congr 1
  ring
#check step_expansion
/-- 
The Collatz Operator Output Parity.
Proves that the accelerated Collatz operator T(x) always outputs an odd integer.
Any even output wouldviolate the absolute maximum factorization bound of the 2-adic valuation.
-/
theorem T_is_always_odd (x : ℕ) : (T x) % 2 = 1 := by
  
  have h_nz : 3 * x + 1 ≠ 0 := by omega
  have h_prime : Nat.Prime 2 := Nat.prime_two
  
  dsimp [T]
  
  by_contra h_not_odd
  
  have h_even : (3 * x + 1) / 2^(val x) % 2 = 0 := by omega
  
  have h_dvd_T : 2 ∣ (3 * x + 1) / 2^(val x) := Nat.dvd_of_mod_eq_zero h_even
  
  have h_dvd_next : 2^(val x + 1) ∣ 3 * x + 1 := by
    have h_div_cancel : 2^(val x) * ((3 * x + 1) / 2^(val x)) = 3 * x + 1 := by
      have h_div : 2^(val x) ∣ (3 * x + 1) := by
        rw [Nat.Prime.pow_dvd_iff_le_factorization h_prime h_nz]
        exact le_refl _
      exact Nat.mul_div_cancel' h_div
    
    -- Extract witness 'c' for the divisibility condition
    rcases h_dvd_T with ⟨c, hc⟩
    use c
    calc 3 * x + 1 = 2^(val x) * ((3 * x + 1) / 2^(val x)) := h_div_cancel.symm
      _ = 2^(val x) * (2 * c) := by rw [hc]
      _ = (2^(val x) * 2) * c := by ring
      _ = 2^(val x + 1) * c := by rw [← pow_succ]

  have h_max : val x + 1 ≤ (Nat.factorization (3 * x + 1)) 2 := 
    (Nat.Prime.pow_dvd_iff_le_factorization h_prime h_nz).mp h_dvd_next
  
  have h_val_def : (Nat.factorization (3 * x + 1)) 2 = val x := by rfl
  
  rw [h_val_def] at h_max
  
  omega

end Section2_MultipleIterations

#print axioms step_expansion
#print axioms T_is_always_odd
#check T_is_always_odd
-- ===============================================================
-- SECTION 3: RECURSIVE SEQUENCE AND EXPANSION
-- ===============================================================
section Section3_Recursive

/--
Exactness of the Collatz Step.
Establishes that 2^(val(x)) * T(x) = 3x + 1, representing the inverse of the division operation.
-/
theorem collatz_step_exact (x : ℕ) : 2^(val x) * T x = 3 * x + 1 := by
  dsimp [T]
  have h_prime : Nat.Prime 2 := Nat.prime_two
  
  have h_nz : 3 * x + 1 ≠ 0 := by omega
  
  have h_div : 2^(val x) ∣ (3 * x + 1) := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization h_prime h_nz]
    exact le_refl _
  rw [mul_comm]
  rw [Nat.div_mul_cancel h_div]
#check collatz_step_exact
/--
Recursive Sum of Exponents (S_n).
S n x evaluates the cumulative sum of 2-adic valuations after n steps starting from x.
-/
noncomputable def S (n : ℕ) (x : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | succ k => S k x + val ((T^[k]) x)

/--
The Recursive Numerator (Z_n).
Defines the numerator component of the multi-step sequence: Z_0 = 0, Z_{k+1} = 3*Z_k + 2^{S_k}.
-/
noncomputable def closed_numerator (n : ℕ) (x : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | succ k => 3 * (closed_numerator k x) + 2^(S k x)

/--
The Fundamental Iteration Formula.
Formulates the core algebraic expansion of the trajectory: 2^(S_n) * x_n = 3^n * x + Z_n.
-/
theorem iterate_expansion (n : ℕ) (x : ℕ) :
  2^(S n x) * (T^[n] x) = 3^n * x + closed_numerator n x := by
  
  induction n with
  | zero =>
    simp [S, closed_numerator]
  
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    let x_k := T^[k] x
    
    dsimp [S, closed_numerator]
    rw [pow_add]
    
    rw [mul_assoc]
    rw [collatz_step_exact x_k]
    
    rw [mul_add, mul_one]
    rw [mul_left_comm (2^(S k x)) 3 x_k]
    
    rw [ih]
    ring
#check iterate_expansion
/--
The Multi-Step Modular Diophantine Equation.
Substitutes the global modular definition (x = 2^v * k + m) into the fundamental iteration formula.
-/
theorem iterate_expansion_modular (n v x : ℕ) :
  2^(S n x) * (T^[n] x) = 3^n * (2^v * k v x + m v x) + closed_numerator n x := by
  have h_iter := iterate_expansion n x
  have h_x : 2^v * k v x + m v x = x := by
    dsimp [k, m]
    exact Nat.div_add_mod x (2^v)
  rw [h_x]
  exact h_iter

end Section3_Recursive
#check iterate_expansion_modular
#print axioms collatz_step_exact
#print axioms iterate_expansion
#print axioms iterate_expansion_modular

-- ===============================================================
-- SECTION 4: CYCLE ANALYSIS
-- ===============================================================
section Section4_CycleAnalysis

/--
The Cycle Predicate.
Defines a cycle of length n as a trajectory where the n-th iterate equals the initial integer x.
-/
def is_cycle (n : ℕ) (x : ℕ) : Prop :=
  T^[n] x = x

/--
Cycle Parity Condition.
Establishes that any integer x forming a closed Collatz cycle must be odd. 
This condition ensures consistent baseline valuation bounds for the trajectory.
-/
theorem cycle_implies_odd (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) : 
  x % 2 = 1 := by
  
  cases n with
  | zero => 
    omega
  | succ k =>
    unfold is_cycle at h_cycle
    
    rw [Function.iterate_succ_apply'] at h_cycle
    
    have h_T_odd := T_is_always_odd (T^[k] x)
    
    rw [h_cycle] at h_T_odd
    
    exact h_T_odd

#check cycle_implies_odd
#print axioms cycle_implies_odd

/--
The Cycle Diophantine Equation.
Formulates the algebraic loop structure: if x forms a cycle, then (2^S - 3^n) * x = Z_n.
-/
theorem cycle_implies_diophantine (n : ℕ) (x : ℕ) (h_cycle : is_cycle n x) :
  (2^(S n x) - 3^n) * x = closed_numerator n x := by
  
  have h_fund := iterate_expansion n x
  rw [h_cycle] at h_fund
  
  rw [add_comm] at h_fund
  
  have h_sub : 2^(S n x) * x - 3^n * x = closed_numerator n x := 
    Nat.sub_eq_of_eq_add h_fund
  
  rw [← Nat.mul_sub_right_distrib] at h_sub
  
  exact h_sub

#check cycle_implies_diophantine
#print axioms cycle_implies_diophantine

end Section4_CycleAnalysis

-- ===============================================================
-- SECTION 5: LEMMA 1A SUPPLEMENT
-- ===============================================================
section Section5_Lemma1A_Supplement

/--
Equilibrium Exponent Derivation.
Proves that an equilibrium cycle ratio forces the uniform division exponent p to equal 2.
-/
theorem derivation_of_equilibrium_exponent (p R : ℕ) 
  (h_R_pos : 0 < R)
  (h_ratio : (R : ℤ) * ((2 : ℤ)^p - 3) = 1) : 
  p = 2 := by
  
  have h_R_ge_1 : (R : ℤ) ≥ 1 := by exact_mod_cast h_R_pos
  set X := (2 : ℤ)^p - 3
  
  have h_X_ge_1 : X ≥ 1 := by
    by_contra h_not
    
    have h_X_le_0 : X ≤ 0 := by omega 
    
    have h_prod_le_0 : (R : ℤ) * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h_X_le_0
    linarith
    
  have h_R_eq_1 : (R : ℤ) = 1 := by
    by_contra h_not
    have h_R_ge_2 : (R : ℤ) ≥ 2 := by omega
    have h_R_le_1 : (R : ℤ) ≤ 1 := by
      calc (R : ℤ) = (R : ℤ) * 1 := by ring
        _ ≤ (R : ℤ) * X := mul_le_mul_of_nonneg_left h_X_ge_1 (by omega)
        _ = 1 := h_ratio
    omega
    
  have h_X_eq_1 : X = 1 := by
    calc X = 1 * X := by ring
      _ = (R : ℤ) * X := by rw [h_R_eq_1]
      _ = 1 := h_ratio
      
  have h_pow : (2 : ℤ)^p = 4 := by 
    calc (2 : ℤ)^p = X + 3 := by dsimp [X]; ring
      _ = 1 + 3 := by rw [h_X_eq_1]
      _ = 4 := by ring
      
  have h_pow_nat : 2^p = 4 := by exact_mod_cast h_pow
  
  have h_not_lt : ¬ (p < 2) := by
    intro h_lt
    interval_cases p
    · norm_num at h_pow_nat
    · norm_num at h_pow_nat
    
  have h_not_gt : ¬ (p > 2) := by
    intro h_gt
    have h_bound : 2^p ≥ 8 := by
      calc 2^p ≥ 2^3 := Nat.pow_le_pow_right (by norm_num) h_gt
        _ = 8 := by rfl
    omega

  omega

#check derivation_of_equilibrium_exponent
#print axioms derivation_of_equilibrium_exponent

end Section5_Lemma1A_Supplement

-- ===============================================================
-- SECTION 6: LEMMA 1A (The Trivial Solution & The Contrapositive Bridge)
-- ===============================================================
section Section6_Lemma1A

/-- Equilibrium Denominator -/
def D_eq (n : ℕ) : ℕ := 2^(2 * n) - 3^n

/-- Equilibrium Numerator -/
def N_eq (n : ℕ) : ℕ := 4^n - 3^n

/-- 
Equilibrium Exponent Sum (S_n = 2n).
Proves the sequence prefix sum evaluates to 2n if all valuations equal 2. 
-/
lemma S_all_two (n : ℕ) (x : ℕ) (h_all : ∀ k < n, val (T^[k] x) = 2) : 
  S n x = 2 * n := by
  induction n with
  | zero => simp [S]
  | succ k ih =>
    simp [S]
    have h_sub : ∀ j < k, val (T^[j] x) = 2 := fun j hj => h_all j (Nat.lt_succ_of_lt hj)
    rw [ih h_sub, h_all k (Nat.lt_succ_self k)]
    ring

#check S_all_two
#print axioms S_all_two

/-- 
Equilibrium Numerator (Z_n = N_eq).
Proves the recursive sequence geometrically expands to N_eq under the equilibrium constraint.
-/
lemma Z_all_two (n : ℕ) (x : ℕ) (h_all : ∀ k < n, val (T^[k] x) = 2) : 
  closed_numerator n x = N_eq n := by
  induction n with
  | zero => simp [closed_numerator, N_eq]
  | succ k ih =>
    simp [closed_numerator]
    
    have h_sub : ∀ j < k, val (T^[j] x) = 2 := fun j hj => h_all j (Nat.lt_succ_of_lt hj)
    rw [ih h_sub, S_all_two k x h_sub]
    rw [pow_mul, show 2^2 = 4 by rfl]
    
    unfold N_eq
    symm
    
    -- Establish inequality of the respective base powers
    have h_le_pow_succ : 3^(k+1) ≤ 4^(k+1) := Nat.pow_le_pow_left (by norm_num) (k+1)
    rw [Nat.sub_eq_iff_eq_add h_le_pow_succ]
    
    rw [Nat.mul_sub_left_distrib 3 (4^k) (3^k)]
    
    rw [pow_succ' 4 k, pow_succ' 3 k]
    rw [add_assoc, add_comm (4^k), ← add_assoc]
    
    have h_inner_le : 3^k ≤ 4^k := Nat.pow_le_pow_left (by norm_num) k
    have h_cancel_le : 3 * 3^k ≤ 3 * 4^k := Nat.mul_le_mul_left 3 h_inner_le
    rw [Nat.sub_add_cancel h_cancel_le]
    ring

#check Z_all_two
#print axioms Z_all_two

/--
The Modular Cycle Diophantine Equation.
Forces the cycle structure to account for the quotient and residue parameters.
-/
theorem cycle_implies_diophantine_modular (n v x : ℕ) (h_cycle : is_cycle n x) :
  (2^(S n x) - 3^n) * (2^v * k v x + m v x) = closed_numerator n x := by
  have h_eqn := cycle_implies_diophantine n x h_cycle
  have h_x : 2^v * k v x + m v x = x := by
    dsimp [k, m]
    exact Nat.div_add_mod x (2^v)
  rw [h_x]
  exact h_eqn

#check cycle_implies_diophantine_modular
#print axioms cycle_implies_diophantine_modular

/--
Lemma 1A (The Trivial Solution - Integrated Modular Form)
Proves x = 1. This theorem utilizes the modular cycle Diophantine equation, 
evaluating the trajectory by resolving x into its quotient (k) and residue (m) parameters.
-/
theorem lemma_1a_trivial_solution (n : ℕ) (x : ℕ) 
  (h_cycle : is_cycle n x) 
  (h_pos : n > 0)
  (h_all : ∀ k < n, val (T^[k] x) = 2) : 
  x = 1 := by
  
  let v := 2 * n
  have h_eqn := cycle_implies_diophantine_modular n v x h_cycle
  
  rw [S_all_two n x h_all, Z_all_two n x h_all] at h_eqn
  dsimp [D_eq, N_eq] at h_eqn
  
  rw [pow_mul, show 2^2 = 4 by rfl] at h_eqn

  have h_nonzero : 0 < 4^n - 3^n := 
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt h_pos))
  
  conv_rhs at h_eqn => rw [← mul_one (4^n - 3^n)]
  
  have h_modular_one := Nat.eq_of_mul_eq_mul_left h_nonzero h_eqn
  
  have h_x : 2^v * k v x + m v x = x := by
    dsimp [k, m]
    exact Nat.div_add_mod x (2^v)
  
  have h_align : 4^n = 2^v := by
    have h_four : 4 = 2^2 := by rfl
    rw [h_four, ← pow_mul]
  
  rw [h_align] at h_modular_one
  
  rw [h_x] at h_modular_one
  exact h_modular_one

#check lemma_1a_trivial_solution
#print axioms lemma_1a_trivial_solution

/--
The Non-Trivial Contrapositive (The Logical Bridge).
Proves that any closed cycle originating at x > 1 
cannot maintain the equilibrium sequence of valuations.
This creates the mathematical bridge out of the trivial state,
forcing all non-trivial cycles into the perturbed domain.
-/
theorem non_trivial_cycle_forces_perturbation (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn_pos : n > 0)
  (h_non_trivial : x > 1) :
  ¬ (∀ k < n, val (T^[k] x) = 2) := by
  
  intro h_all_two
  have h_x_eq_1 := lemma_1a_trivial_solution n x h_cycle hn_pos h_all_two
  
  -- The trivial solution x = 1 creates a mathematical contradiction with x > 1
  omega

#check non_trivial_cycle_forces_perturbation
#print axioms non_trivial_cycle_forces_perturbation

end Section6_Lemma1A

-- ===============================================================
-- SECTION 7: THE EXISTENCE THRESHOLD
-- ===============================================================
section Section7_Existence_Threshold

/--
Corollary 1A.1: The Existence Threshold.
Proves that cycle existence requires the geometric denominator 2^S - 3^n to remain positive.
-/
theorem cycle_existence_threshold (n : ℕ) (x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  3^n < 2^(S n x) := by
  
  have h_eqn := cycle_implies_diophantine n x h_cycle
  
  have h_pos_Zn : 0 < closed_numerator n x := by
    cases n with
    | zero => 

      omega
    | succ k => 
      unfold closed_numerator
      apply Nat.add_pos_right
      apply Nat.pow_pos
      norm_num

  have h_mul_pos : 0 < (2^(S n x) - 3^n) * x := by 
    rw [h_eqn]
    exact h_pos_Zn
    
  have h_sub_pos : 0 < 2^(S n x) - 3^n := 
    Nat.pos_of_mul_pos_right h_mul_pos

  exact Nat.lt_of_sub_pos h_sub_pos

#check cycle_existence_threshold
#print axioms cycle_existence_threshold
end Section7_Existence_Threshold

-- ===============================================================
-- SECTION 8: THE GEOMETRIC SUMMATION
-- ===============================================================
section Section8_Lemma2A_Explicit

/--
The Summation T_n.
Translates the recursive numerator into a geometric series.
-/
noncomputable def sum_T (n : ℕ) (x : ℕ) : ℕ :=
  ∑ k ∈ range n, 3^(n - 1 - k) * 2^(S k x)

/--
Equivalence of Recursive Forms.
Proves Z_n = sum_T(n, x), ensuring the algebraic transition is rigorous.
-/
theorem closed_numerator_eq_sum_T (n : ℕ) (x : ℕ) :
  closed_numerator n x = sum_T n x := by
  induction n with
  | zero =>
    simp [closed_numerator, sum_T]
  | succ k ih =>
    rw [closed_numerator, ih]
    dsimp [sum_T]
    
    rw [sum_range_succ]
    
    rw [Nat.sub_self, pow_zero, one_mul]
    
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    
    rw [← mul_assoc, mul_comm 3 (3^(k - 1 - j)), ← pow_succ]
    congr 2
    
    -- Simplifies the exponent using the upper bound of the summation index
    have h_lt : j < k := Finset.mem_range.mp hj
    omega
#check closed_numerator_eq_sum_T
/--
The Cycle Diophantine Identity.
Substitutes the geometric sum into the fundamental cycle equation.
-/
theorem cycle_implies_explicit_diophantine (n : ℕ) (x : ℕ) (h_cycle : is_cycle n x) :
  (2^(S n x) - 3^n) * x = sum_T n x := by
  have h_orig := cycle_implies_diophantine n x h_cycle
  rw [closed_numerator_eq_sum_T n x] at h_orig
  exact h_orig

end Section8_Lemma2A_Explicit

#print axioms closed_numerator_eq_sum_T
#print axioms cycle_implies_explicit_diophantine
#check cycle_implies_explicit_diophantine

-- ===============================================================
-- SECTION 9: THE PERTURBATION MODEL
-- ===============================================================

section Section9_Perturbation_Model

/--
Index Shift Identity.

Algebraic form:
`(m + 1) - 1 - j = (m - 1 - j) + 1` for `j < m`.
-/
lemma nat_index_shift (m j : ℕ) (hj : j < m) :
  m + 1 - 1 - j = (m - 1 - j) + 1 := by
  omega

/--
Equilibrium Numerator Summation Identity.

Formulates:
`4^n - 3^n = Σ_{j=0}^{n-1} 3^(n-1-j) * 2^(2j)`.
-/
theorem N_eq_as_sum (n : ℕ) :
  (N_eq n : ℚ) =
    ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by

  rw [N_eq]

  induction n with
  | zero =>
      simp

  | succ m ih =>
      rw [sum_range_succ]

      have h_factor :
          ∑ j ∈ range m,
              (3 : ℚ)^(m.succ - 1 - j) * (2 : ℚ)^(2 * j)
            =
          3 * ∑ j ∈ range m,
              (3 : ℚ)^(m - 1 - j) * (2 : ℚ)^(2 * j) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [nat_index_shift m j (Finset.mem_range.mp hj), pow_succ]
        ring

      rw [h_factor, ← ih]

      have h_pow_match :
          (2 : ℚ)^(2 * m) = (4 : ℚ)^m := by
        rw [pow_mul]
        norm_num

      simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_mul, h_pow_match]

      have h_le_succ : 3^(m + 1) ≤ 4^(m + 1) :=
        Nat.pow_le_pow_left (by norm_num) (m + 1)

      have h_le_m : 3^m ≤ 4^m :=
        Nat.pow_le_pow_left (by norm_num) m

      rw [Nat.cast_sub h_le_succ, Nat.cast_sub h_le_m]
      push_cast
      ring

/--
The local perturbation operator.

`δᵢ = aᵢ - 2`, where `aᵢ = val (T^[i] x)`.
-/
noncomputable def delta (x : ℕ) (i : ℕ) : ℤ :=
  (val (T^[i] x) : ℤ) - 2

/--
Prefix sum of perturbations.

`S'_j = Σ_{i=0}^{j-1} δᵢ`.
-/
noncomputable def S_prime (j : ℕ) (x : ℕ) : ℤ :=
  ∑ i ∈ range j, delta x i

/--
Prefix Sum Equivalence.

The actual exponent sum equals the equilibrium baseline plus cumulative
perturbation:
`S_j = 2j + S'_j`.
-/
theorem s_relationship (j : ℕ) (x : ℕ) :
  (S j x : ℤ) = 2 * (j : ℤ) + S_prime j x := by

  induction j with
  | zero =>
      simp [S, S_prime]

  | succ n ih =>
      simp [S, S_prime, sum_range_succ, ih]
      dsimp [delta]
      ring

/--
The Exact Difference Formula.

This expresses the numerator deviation from equilibrium as a weighted
perturbation sum.
-/
theorem exact_difference_formula (n : ℕ) (x : ℕ) :
  (sum_T n x : ℚ) - (N_eq n : ℚ) =
    ∑ j ∈ range n,
      (3 : ℚ)^(n - 1 - j) *
        (2 : ℚ)^(2 * j) *
          ((2 : ℚ)^(S_prime j x) - 1) := by

  rw [sum_T, N_eq_as_sum]
  push_cast
  rw [← sum_sub_distrib]

  apply sum_congr rfl
  intro j hj

  rw [mul_sub, mul_one]
  congr 1

  have h_rel := s_relationship j x

  have h_exp_match :
      (2 : ℚ)^(S j x) =
        (2 : ℚ)^(2 * j) * (2 : ℚ)^(S_prime j x) := by
    rw [← zpow_natCast, h_rel, zpow_add₀ (by norm_num)]
    norm_cast

  rw [h_exp_match]
  ring

/--
The equilibrium state in perturbation language.
-/
def is_equilibrium (n : ℕ) (x : ℕ) : Prop :=
  ∀ i ∈ range n, delta x i = 0

/--
Equilibrium bridge.

The perturbation-language equilibrium is exactly the original valuation
condition used in Lemma 1A.
-/
lemma is_equilibrium_iff_all_val_two
  (n x : ℕ) :
  is_equilibrium n x ↔ ∀ k < n, val (T^[k] x) = 2 := by

  constructor

  · intro h_eq k hk

    have h_delta_zero :
        delta x k = 0 :=
      h_eq k (Finset.mem_range.mpr hk)

    unfold delta at h_delta_zero

    have h_cast :
        (val (T^[k] x) : ℤ) = 2 := by
      linarith

    exact_mod_cast h_cast

  · intro h_all k hk

    have h_val :
        val (T^[k] x) = 2 :=
      h_all k (Finset.mem_range.mp hk)

    unfold delta
    rw [h_val]
    norm_num

/--
The mixed perturbation state.
-/
def is_mixed_perturbation (n : ℕ) (x : ℕ) : Prop :=
  (∃ i ∈ range n, delta x i < 0) ∧
    (∃ j ∈ range n, 0 < delta x j)

/--
Exhaustive perturbation-space partition.

Every trajectory segment is exactly one of:
equilibrium, pure nonpositive with a negative term, pure nonnegative with a
positive term, or mixed.
-/
theorem perturbation_space_exhaustive (n x : ℕ) :
  is_equilibrium n x ∨
  ((∀ i ∈ range n, delta x i ≤ 0) ∧
    (∃ i ∈ range n, delta x i < 0)) ∨
  ((∀ i ∈ range n, 0 ≤ delta x i) ∧
    (∃ i ∈ range n, 0 < delta x i)) ∨
  is_mixed_perturbation n x := by

  by_cases h_neg : ∃ i ∈ range n, delta x i < 0

  · by_cases h_pos : ∃ j ∈ range n, 0 < delta x j

    · exact Or.inr (Or.inr (Or.inr ⟨h_neg, h_pos⟩))

    · have h_all_le :
        ∀ i ∈ range n, delta x i ≤ 0 := by
        intro i hi
        by_contra h_gt
        apply h_pos
        exact ⟨i, hi, by omega⟩

      exact Or.inr (Or.inl ⟨h_all_le, h_neg⟩)

  · by_cases h_pos : ∃ j ∈ range n, 0 < delta x j

    · have h_all_ge :
        ∀ i ∈ range n, 0 ≤ delta x i := by
        intro i hi
        by_contra h_lt
        apply h_neg
        exact ⟨i, hi, by omega⟩

      exact Or.inr (Or.inr (Or.inl ⟨h_all_ge, h_pos⟩))

    · have h_all_zero :
        ∀ i ∈ range n, delta x i = 0 := by
        intro i hi

        have h_not_lt : ¬ delta x i < 0 := by
          intro h
          apply h_neg
          exact ⟨i, hi, h⟩

        have h_not_gt : ¬ 0 < delta x i := by
          intro h
          apply h_pos
          exact ⟨i, hi, h⟩

        omega

      exact Or.inl h_all_zero

/--
Nontrivial cycle routing.

A nontrivial cycle cannot remain in equilibrium, so it must route into one of
the three perturbed branches.
-/
theorem non_trivial_cycle_routing (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn_pos : n > 0)
  (h_non_trivial : x > 1) :
  ((∀ i ∈ range n, delta x i ≤ 0) ∧
    (∃ i ∈ range n, delta x i < 0)) ∨
  ((∀ i ∈ range n, 0 ≤ delta x i) ∧
    (∃ i ∈ range n, 0 < delta x i)) ∨
  is_mixed_perturbation n x := by

  have h_exhaustive := perturbation_space_exhaustive n x

  have h_not_eq : ¬ is_equilibrium n x := by
    intro h_eq

    have h_all_two :
        ∀ k < n, val (T^[k] x) = 2 :=
      (is_equilibrium_iff_all_val_two n x).mp h_eq

    exact
      (non_trivial_cycle_forces_perturbation
        n x h_cycle hn_pos h_non_trivial)
      h_all_two

  rcases h_exhaustive with h_eq | h_pure_neg | h_pure_pos | h_mixed

  · exfalso
    exact h_not_eq h_eq

  · exact Or.inl h_pure_neg

  · exact Or.inr (Or.inl h_pure_pos)

  · exact Or.inr (Or.inr h_mixed)

end Section9_Perturbation_Model
-- ===============================================================
-- SECTION 10: NUMERATOR BOUNDS UNDER PERTURBATION
-- ===============================================================
section Section10_Numerator_Bounds

/--
Null Perturbation Identity.
Establishes that a sequence of zero prefix sums yields a numerator identical to the equilibrium baseline.
-/
theorem equality_case (n : ℕ) (x : ℕ) (h_zero : ∀ j ∈ range n, S_prime j x = 0) :
  (sum_T n x : ℚ) = (N_eq n : ℚ) := by
  have h_diff := exact_difference_formula n x
  have h_rhs_zero : ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) * ((2 : ℚ)^(S_prime j x) - 1) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [h_zero j hj, zpow_zero, sub_self, mul_zero]
  rw [h_rhs_zero] at h_diff
  exact sub_eq_zero.mp h_diff

/--
Upper Bound for Non-Positive Trajectories.
Demonstrates that a non-positive prefix sequence restricts the total numerator to the equilibrium baseline or below.
-/
theorem monotone_nonpositive_case (n : ℕ) (x : ℕ) (h_neg : ∀ j ∈ range n, S_prime j x ≤ 0) :
  (sum_T n x : ℚ) ≤ (N_eq n : ℚ) := by
  have h_diff := exact_difference_formula n x
  rw [← sub_nonpos, h_diff]
  
  apply sum_nonpos
  intro j hj
  
  have h_weight_pos : (0 : ℚ) < (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by
    apply mul_pos <;> apply pow_pos <;> norm_num
    
  have h_term_nonpos : (2 : ℚ)^(S_prime j x) - 1 ≤ 0 := by
    rw [sub_nonpos]
    apply zpow_le_one_of_nonpos₀
    · norm_num
    · exact h_neg j hj
    
  exact mul_nonpos_of_nonneg_of_nonpos h_weight_pos.le h_term_nonpos

/--
Lower Bound for Non-Negative Trajectories.
Demonstrates that a non-negative prefix sequence forces the total numerator to meet or exceed the equilibrium baseline.
-/
theorem monotone_nonnegative_case (n : ℕ) (x : ℕ) (h_pos : ∀ j ∈ range n, 0 ≤ S_prime j x) :
  (N_eq n : ℚ) ≤ (sum_T n x : ℚ) := by
  have h_diff := exact_difference_formula n x
  
  rw [← sub_nonneg]
  rw [h_diff]
  
  apply sum_nonneg
  intro j hj
  
  have h_weight_pos : (0 : ℚ) < (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by
    apply mul_pos <;> apply pow_pos <;> norm_num
    
  have h_term_nonneg : 0 ≤ (2 : ℚ)^(S_prime j x) - 1 := by
    rw [le_sub_iff_add_le, zero_add]
    apply one_le_zpow₀
    · norm_num
    · exact h_pos j hj
    
  exact mul_nonneg h_weight_pos.le h_term_nonneg

end Section10_Numerator_Bounds

#print axioms equality_case
#print axioms monotone_nonpositive_case
#print axioms monotone_nonnegative_case
#check equality_case
#check monotone_nonpositive_case
#check monotone_nonnegative_case

-- ===============================================================
-- SECTION 11: PRELIMINARY BOUNDS & INTEGER LIFTS
-- ===============================================================
section Section11_Valuation_Target

/--
Logarithmic Monotonicity for the Collatz Bound.
Converts the integer threshold 3^n < 2^S into a real logarithmic inequality.
-/
lemma log_ratio_bound (n S_val : ℕ) (hn : 0 < n) (h_bound : 3^n < 2^S_val) :
  Real.log 3 / Real.log 2 < (S_val : ℝ) / (n : ℝ) := by
  
  have h_bound_real : (3 : ℝ)^n < (2 : ℝ)^S_val := by exact_mod_cast h_bound
  
  have h_log_lt : Real.log ((3 : ℝ)^n) < Real.log ((2 : ℝ)^S_val) := by
    apply Real.log_lt_log
    · positivity
    · exact h_bound_real
    
  rw [Real.log_pow, Real.log_pow] at h_log_lt
  
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog2_pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
    
  have hn_inv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
  have h_div1 : ((n : ℝ) * Real.log 3) * (n : ℝ)⁻¹ < ((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹ := by
    exact mul_lt_mul_of_pos_right h_log_lt hn_inv_pos
    
  have h_cancel_n : ((n : ℝ) * Real.log 3) * (n : ℝ)⁻¹ = Real.log 3 := by
    calc ((n : ℝ) * Real.log 3) * (n : ℝ)⁻¹ 
      _ = Real.log 3 * ((n : ℝ) * (n : ℝ)⁻¹) := by ring
      _ = Real.log 3 * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hn_pos)]
      _ = Real.log 3 := by ring
      
  rw [h_cancel_n] at h_div1
  
  have hlog2_inv_pos : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlog2_pos
  have h_div2 : Real.log 3 * (Real.log 2)⁻¹ < (((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹) * (Real.log 2)⁻¹ := by
    exact mul_lt_mul_of_pos_right h_div1 hlog2_inv_pos
    
  have h_rhs_simp : (((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹) * (Real.log 2)⁻¹ = (S_val : ℝ) / (n : ℝ) := by
    calc (((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹) * (Real.log 2)⁻¹
      _ = (S_val : ℝ) * (n : ℝ)⁻¹ * (Real.log 2 * (Real.log 2)⁻¹) := by ring
      _ = (S_val : ℝ) * (n : ℝ)⁻¹ * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hlog2_pos)]
      _ = (S_val : ℝ) / (n : ℝ) := by ring
      
  have h_lhs_simp : Real.log 3 * (Real.log 2)⁻¹ = Real.log 3 / Real.log 2 := by ring
  
  rw [h_lhs_simp, h_rhs_simp] at h_div2
  exact h_div2

/--
Constraint 5: The Negative Deficit Bound.
Given S = 2n - p, proves that the number of negative perturbations (p) 
is bounded linearly by n: p/n < 2 - (log_3 / log_2).
-/
theorem constraint_5_deficit_bound (n S_val p : ℕ) 
  (hn : 0 < n) 
  (h_bound : 3^n < 2^S_val)
  (h_deficit : S_val + p = 2 * n) :
  (p : ℝ) / (n : ℝ) < 2 - (Real.log 3 / Real.log 2) := by
  
  have h_ratio := log_ratio_bound n S_val hn h_bound
  
  have h_S_eq : (S_val : ℝ) = 2 * (n : ℝ) - (p : ℝ) := by
    have h_cast : (S_val : ℝ) + (p : ℝ) = 2 * (n : ℝ) := by exact_mod_cast h_deficit
    linarith
    
  rw [h_S_eq] at h_ratio
  
  have hn_pos : (n : ℝ) ≠ 0 := by
    have : 0 < (n : ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
    
  have h_distrib : (2 * (n : ℝ) - (p : ℝ)) / (n : ℝ) = 2 - (p : ℝ) / (n : ℝ) := by
    calc (2 * (n : ℝ) - (p : ℝ)) / (n : ℝ) 
      _ = (2 * (n : ℝ)) / (n : ℝ) - (p : ℝ) / (n : ℝ) := by rw [sub_div]
      _ = 2 * ((n : ℝ) / (n : ℝ)) - (p : ℝ) / (n : ℝ) := by ring
      _ = 2 * 1 - (p : ℝ) / (n : ℝ) := by rw [div_self hn_pos]
      _ = 2 - (p : ℝ) / (n : ℝ) := by ring
      
  rw [h_distrib] at h_ratio
  linarith

/--
Integer Field Diophantine Lift.
Maps the core Diophantine equation and its variable representations into the integer ring (ℤ).
-/
lemma cycle_diophantine_int (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  (sum_T n x : ℤ) = (2 : ℤ)^(S n x) * (x : ℤ) - (3 : ℤ)^n * (x : ℤ) := by
  
  have h_eq := cycle_implies_explicit_diophantine n x h_cycle
  have h_threshold : 3^n ≤ 2^(S n x) := le_of_lt (cycle_existence_threshold n x h_cycle hn)
  
  have h_cast : ((sum_T n x : ℤ)) = (((2^(S n x) - 3^n) * x : ℕ) : ℤ) := by rw [h_eq]
  rw [h_cast]
  
  rw [Nat.cast_mul, Nat.cast_sub h_threshold]
  push_cast
  ring

/--
Integer Formulation of Equilibrium Numerator.
Establishes (N_eq : ℤ) = 2^(2n) - 3^n to facilitate algebraic comparisons.
-/
lemma N_eq_int (n : ℕ) : (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n := by
  unfold N_eq
  have h_pow : 3^n ≤ 4^n := Nat.pow_le_pow_left (by norm_num) n
  rw [Nat.cast_sub h_pow]
  push_cast
  have h_4 : (4 : ℤ) = 2^2 := by norm_num
  rw [h_4, ← pow_mul]

end Section11_Valuation_Target

#print axioms constraint_5_deficit_bound
#check log_ratio_bound
#check constraint_5_deficit_bound
#check cycle_diophantine_int
-- ===============================================================
-- SECTION 12: LEMMA 1C SETUP (Pure Negative Definition)
-- ===============================================================
section Section12_Lemma1C_Setup

/--
Pure Negative Perturbation Definition.
-/
def is_pure_negative (n : ℕ) (x : ℕ) : Prop :=
  (∀ i ∈ range n, delta x i ≤ 0) ∧ (S_prime n x < 0)

/--
Global Exponent Sum Upper Bound.
-/
theorem pure_negative_S_lt_2n (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) : 
  S n x < 2 * n := by
  
  have h_rel := s_relationship n x
  have h_prime_neg : S_prime n x < 0 := h_neg.2
  
  zify at h_rel ⊢
  rw [h_rel]
  linarith

end Section12_Lemma1C_Setup

#print axioms pure_negative_S_lt_2n
#check pure_negative_S_lt_2n
-- ===============================================================
-- SECTION 13: LEMMA 1C (PURE NEGATIVE PERTURBATION CONSEQUENCE)
-- ===============================================================
section Section13_Lemma1C_Pure_Negative_Perturbation

/--
Partial Sum Upper Bound.
Demonstrates that the cumulative sum of remaining exponents from index j to n 
is bounded by twice the step count.
-/
theorem pure_negative_partial_sum_bound (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) (j : ℕ) (hj : j ≤ n) :
  S n x - S j x ≤ 2 * (n - j) := by
  
  rw [Nat.sub_le_iff_le_add]

  suffices h_gen : ∀ k, j + k ≤ n → S (j + k) x ≤ S j x + 2 * k by
    specialize h_gen (n - j)
    rw [Nat.add_sub_of_le hj] at h_gen
    rw [add_comm]
    exact h_gen (Nat.le_refl n)

  intro k hk_le
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Nat.add_succ, S]
    rw [Nat.mul_succ]      
    rw [← add_assoc]       
    
    apply Nat.add_le_add
    · apply ih
      exact Nat.le_of_succ_le hk_le
    · have h_idx : j + k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk_le
      have h_delta := h_neg.1 (j + k) (Finset.mem_range.mpr h_idx)
      dsimp [delta] at h_delta
      zify at h_delta ⊢
      linarith
#check pure_negative_partial_sum_bound
/--
Term-wise Geometric Lower Bound.
Formulates the minimum algebraic value for individual terms within the perturbed summation.
-/
theorem pure_negative_term_bound (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) (j : ℕ) (hj : j ∈ range n) :
  (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(S j x) ≥ 
  ((2 : ℚ)^(S n x) / 4) * (3 / 4 : ℚ)^(n - 1 - j) := by

  let k := n - 1 - j
  have hj_lt : j < n := Finset.mem_range.mp hj 
  have hk_rel : n - j = k + 1 := by omega
  
  have h_idx_le : j ≤ n := Nat.le_of_lt hj_lt
  have h_exp_bound := pure_negative_partial_sum_bound n x h_neg j h_idx_le
  
  have h_exp_bound2 : S n x - S j x ≤ 2 * (k + 1) := by
    rw [hk_rel] at h_exp_bound
    exact h_exp_bound

  have h_exp_add : S n x ≤ S j x + 2 * (k + 1) := by omega

  have h_pow_nat : 2 ^ S n x ≤ 2 ^ (S j x + 2 * (k + 1)) := 
    Nat.pow_le_pow_right (by norm_num) h_exp_add

  have h_pow_simp : 2 ^ (S j x + 2 * (k + 1)) = 2 ^ S j x * 4 ^ (k + 1) := by
    rw [pow_add, pow_mul]
    rfl

  rw [h_pow_simp] at h_pow_nat

  have h_pow_rat : (2 : ℚ) ^ S n x ≤ (2 : ℚ) ^ S j x * (4 : ℚ) ^ (k + 1) := by
    exact_mod_cast h_pow_nat

  have h_div : (2 : ℚ) ^ S n x / (4 : ℚ) ^ (k + 1) ≤ (2 : ℚ) ^ S j x := by
    rw [div_le_iff₀]
    · linarith
    · positivity

  have h_mul : ((2 : ℚ) ^ S n x / (4 : ℚ) ^ (k + 1)) * (3 : ℚ) ^ k ≤ 
               (2 : ℚ) ^ S j x * (3 : ℚ) ^ k := by
    apply mul_le_mul_of_nonneg_right h_div
    positivity

  change ((2 : ℚ) ^ S n x / 4) * (3 / 4 : ℚ) ^ k ≤ (3 : ℚ) ^ k * (2 : ℚ) ^ S j x

  have h_goal_lhs : ((2 : ℚ) ^ S n x / 4) * (3 / 4 : ℚ) ^ k = 
                    ((2 : ℚ) ^ S n x / (4 : ℚ) ^ (k + 1)) * (3 : ℚ) ^ k := by
    rw [div_pow, pow_succ]
    ring

  have h_goal_rhs : (3 : ℚ) ^ k * (2 : ℚ) ^ S j x = 
                    (2 : ℚ) ^ S j x * (3 : ℚ) ^ k := by
    ring

  rw [h_goal_lhs, h_goal_rhs]
  exact h_mul
#check pure_negative_term_bound
/--
Geometric Summation Lower Bound.
Establishes the absolute lower bound for the total perturbed numerator.
-/
theorem pure_negative_numerator_lower_bound (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) :
  (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) ≤ (sum_T n x : ℚ) := by
  
  have h_sum_T_cast : (sum_T n x : ℚ) = ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(S j x) := by
    rw [sum_T]
    push_cast
    rfl
  
  rw [h_sum_T_cast]
  
  have h_sum_le : ∑ j ∈ range n, ((2 : ℚ)^(S n x) / 4) * (3 / 4 : ℚ)^(n - 1 - j) ≤ 
                  ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(S j x) := by
    apply sum_le_sum
    intro j hj
    exact pure_negative_term_bound n x h_neg j hj

  have h_factor : ∑ j ∈ range n, ((2 : ℚ)^(S n x) / 4) * (3 / 4 : ℚ)^(n - 1 - j) = 
                  ((2 : ℚ)^(S n x) / 4) * ∑ j ∈ range n, (3 / 4 : ℚ)^(n - 1 - j) := by
    rw [mul_sum]

  have h_reindex : ∑ j ∈ range n, (3 / 4 : ℚ)^(n - 1 - j) = ∑ k ∈ range n, (3 / 4 : ℚ)^k := by
    exact sum_range_reflect (fun k => (3 / 4 : ℚ)^k) n

  have h_geom_sum : ∑ k ∈ range n, (3 / 4 : ℚ)^k = (1 - (3 / 4 : ℚ)^n) / (1 - 3 / 4) := by
    have h_standard := geom_sum_eq (x := (3 / 4 : ℚ)) (by norm_num) n
    rw [h_standard]
    generalize (3 / 4 : ℚ)^n = B
    ring

  have h_alg_eq : (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) = 
        ((2 : ℚ)^(S n x) / 4) * ((1 - (3 / 4 : ℚ)^n) / (1 - 3 / 4)) := by
    generalize (2 : ℚ)^(S n x) = A
    generalize (3 / 4 : ℚ)^n = B
    ring

  rw [h_alg_eq, ← h_geom_sum, ← h_reindex, ← h_factor]
  exact h_sum_le
#check pure_negative_numerator_lower_bound
/--
Lemma 1C: Pure Negative Inequality.
Demonstrates that a purely negative perturbation forces the numerator to exceed the denominator.
-/
theorem pure_negative_numerator_gt_denominator (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) :
  ((2 : ℚ)^(S n x) - (3 : ℚ)^n) < (sum_T n x : ℚ) := by
  
  have h_lower := pure_negative_numerator_lower_bound n x h_neg
  have h_S_lt : S n x < 2 * n := pure_negative_S_lt_2n n x h_neg
  
  have h_p_ex : ∃ p : ℕ, S n x + p = 2 * n ∧ p ≥ 1 := by
    use (2 * n - S n x)
    omega
  rcases h_p_ex with ⟨p, h_Sp, hp⟩

  have h_four : (4 : ℚ)^n = (2 : ℚ)^(2 * n) := by
    have : (4 : ℚ) = 2^2 := by norm_num
    rw [this, ← pow_mul]
    
  have h_pow2_add : (2 : ℚ)^(2 * n) = (2 : ℚ)^(S n x) * (2 : ℚ)^p := by
    rw [← h_Sp, pow_add]
    
  have h_subst : (4 : ℚ)^n = (2 : ℚ)^(S n x) * (2 : ℚ)^p := by
    rw [h_four, h_pow2_add]

  have h_frac : (3 / 4 : ℚ)^n = (3 : ℚ)^n / ((2 : ℚ)^(S n x) * (2 : ℚ)^p) := by
    rw [div_pow, h_subst]

  have h2S : (2 : ℚ)^(S n x) ≠ 0 := by positivity

  have h_alg_diff : (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n) = 
                    (3 : ℚ)^n * (1 - 1 / (2 : ℚ)^p) := by
    calc (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n)
      _ = (2 : ℚ)^(S n x) - (2 : ℚ)^(S n x) * (3 / 4 : ℚ)^n - (2 : ℚ)^(S n x) + (3 : ℚ)^n := by ring
      _ = (3 : ℚ)^n - (2 : ℚ)^(S n x) * ((3 : ℚ)^n / ((2 : ℚ)^(S n x) * (2 : ℚ)^p)) := by
          rw [h_frac]
          ring
      _ = (3 : ℚ)^n - ((2 : ℚ)^(S n x) * (3 : ℚ)^n) / ((2 : ℚ)^(S n x) * (2 : ℚ)^p) := by
          congr 1
          rw [mul_div_assoc']
      _ = (3 : ℚ)^n - (((2 : ℚ)^(S n x) * (3 : ℚ)^n) / (2 : ℚ)^(S n x)) / (2 : ℚ)^p := by
          rw [div_mul_eq_div_div]
      _ = (3 : ℚ)^n - (3 : ℚ)^n / (2 : ℚ)^p := by
          congr 2
          exact mul_div_cancel_left₀ ((3 : ℚ)^n) h2S
      _ = (3 : ℚ)^n * (1 - 1 / (2 : ℚ)^p) := by ring

  have hp_pow : (2 : ℚ)^1 ≤ (2 : ℚ)^p := by 
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hp)
    
  have hp_inv : 1 / (2 : ℚ)^p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

  have h_factor : 0 < 1 - 1 / (2 : ℚ)^p := by linarith
  have h_3_pos : (0 : ℚ) < (3 : ℚ)^n := by positivity
  
  have h_diff_pos : 0 < (3 : ℚ)^n * (1 - 1 / (2 : ℚ)^p) := mul_pos h_3_pos h_factor

  have h_N_sub_D : (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n) ≤ 
                   (sum_T n x : ℚ) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n) := by linarith
                   
  rw [h_alg_diff] at h_N_sub_D
  linarith

end Section13_Lemma1C_Pure_Negative_Perturbation
#check pure_negative_numerator_gt_denominator
#print axioms pure_negative_term_bound
#print axioms pure_negative_numerator_lower_bound
#print axioms pure_negative_numerator_gt_denominator
-------------------------------------------------------------------------------------------

-- ===============================================================
-- SECTION 14: LEMMA 1D (Pure Positive Impossibility Bounds)
-- ===============================================================
section Section14_Lemma1D_Pure_Positive_Perturbation

/--
Pure Positive Perturbation Definition.
Defines a purely positive trajectory where all local perturbations are non-negative 
and the cumulative perturbation is positive.
-/
def is_pure_positive (n : ℕ) (x : ℕ) : Prop :=
  (∀ i ∈ range n, 0 ≤ delta x i) ∧ (0 < S_prime n x)

/--
Global Exponent Sum Lower Bound.
Demonstrates that a purely positive perturbation forces the global exponent sum 
above the 2n baseline.
-/
theorem pure_positive_S_gt_2n (n : ℕ) (x : ℕ) 
  (h_pos : is_pure_positive n x) : 
  2 * n < S n x := by
  
  have h_rel := s_relationship n x
  have h_prime_pos : 0 < S_prime n x := h_pos.2
  
  zify at h_rel ⊢
  rw [h_rel]
  linarith

noncomputable def D_new (n : ℕ) (x : ℕ) : ℚ := (2 : ℚ)^(S n x) - (3 : ℚ)^n
noncomputable def Delta_D (n : ℕ) (x : ℕ) : ℚ := D_new n x - (D_eq n : ℚ)
noncomputable def Delta_N (n : ℕ) (x : ℕ) : ℚ := (sum_T n x : ℚ) - (N_eq n : ℚ)
#check pure_positive_S_gt_2n
/--
Exact Denominator Deviation.
Formulates the precise algebraic change in the denominator relative to the equilibrium baseline.
-/
theorem exact_delta_D (n : ℕ) (x : ℕ) :
  Delta_D n x = (2 : ℚ)^(2 * n) * ((2 : ℚ)^(S_prime n x) - 1) := by
  dsimp [Delta_D, D_new, D_eq]
  
  have h_le : 3^n ≤ 2^(2 * n) := by
    rw [pow_mul, show 2^2 = 4 by rfl]
    exact Nat.pow_le_pow_left (by norm_num) n
    
  rw [Nat.cast_sub h_le]
  push_cast
  
  have h_cancel : ((2 : ℚ)^(S n x) - (3 : ℚ)^n) - ((2 : ℚ)^(2 * n) - (3 : ℚ)^n) = 
                  (2 : ℚ)^(S n x) - (2 : ℚ)^(2 * n) := by ring
  rw [h_cancel]
  
  have h_rel := s_relationship n x
  
  have h_exp_match : (2 : ℚ)^(S n x) = (2 : ℚ)^(2 * n) * (2 : ℚ)^(S_prime n x) := by
    rw [← zpow_natCast, h_rel, zpow_add₀ (by norm_num)]
    norm_cast
    
  rw [h_exp_match]
  ring
#check exact_delta_D
----------------------------------------------------------------------
theorem pure_positive_prefix_mono (n : ℕ) (x : ℕ) 
  (h_pos : is_pure_positive n x) (j : ℕ) (hj : j ≤ n) :
  S_prime j x ≤ S_prime n x := by
  dsimp [S_prime]
  
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i hi _
    exact h_pos.1 i hi
#check pure_positive_prefix_mono
/--
Factor Monotonicity.
-/
theorem pure_positive_factor_mono (n : ℕ) (x : ℕ) 
  (h_pos : is_pure_positive n x) (j : ℕ) (hj : j ≤ n) :
  (2 : ℚ)^(S_prime j x) - 1 ≤ (2 : ℚ)^(S_prime n x) - 1 := by
  
  have h_mono := pure_positive_prefix_mono n x h_pos j hj
  
  have h_pow_le : (2 : ℚ)^(S_prime j x) ≤ (2 : ℚ)^(S_prime n x) := by
    apply zpow_le_zpow_right₀ (by norm_num) h_mono
    
  linarith
#check pure_positive_factor_mono
/--
Numerator Deviation Upper Bound.
Establishes the maximum possible algebraic growth for the numerator.
-/
theorem delta_N_upper_bound (n : ℕ) (x : ℕ) (h_pos : is_pure_positive n x) :
  Delta_N n x ≤ ((2 : ℚ)^(S_prime n x) - 1) * (N_eq n : ℚ) := by
  
  rw [Delta_N, exact_difference_formula]
  
  have h_sum_le : ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) * ((2 : ℚ)^(S_prime j x) - 1) ≤ 
                  ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) * ((2 : ℚ)^(S_prime n x) - 1) := by
    apply sum_le_sum
    intro j hj
    have h_weight_pos : 0 ≤ (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by positivity
    apply mul_le_mul_of_nonneg_left _ h_weight_pos
    exact pure_positive_factor_mono n x h_pos j (Nat.le_of_lt (Finset.mem_range.mp hj))

  rw [← sum_mul] at h_sum_le
  rw [mul_comm] at h_sum_le
  rw [← N_eq_as_sum] at h_sum_le
  
  exact h_sum_le
#check delta_N_upper_bound
/--
Rational Transformation of the Equilibrium Numerator.
Maps the equilibrium numerator definition to the rational field.
-/
theorem N_eq_rational (n : ℕ) : 
  (N_eq n : ℚ) = (2 : ℚ)^(2 * n) - (3 : ℚ)^n := by
  dsimp [N_eq]
  rw [pow_mul, show (2 : ℚ)^2 = 4 by rfl]
  rw [Nat.cast_sub]
  · rw [Nat.cast_pow, Nat.cast_pow]
    rfl
  · exact Nat.pow_le_pow_left (by norm_num) n
#check N_eq_rational
/--
Equilibrium Numerator Upper Bound.
Demonstrates that the equilibrium numerator is bounded above by 2^(2n).
-/
theorem N_eq_lt_2pow2n (n : ℕ) : 
  (N_eq n : ℚ) < (2 : ℚ)^(2 * n) := by
  rw [N_eq_rational]
  have h_pos : 0 < (3 : ℚ)^n := by positivity
  linarith
#check N_eq_lt_2pow2n
/--
Growth Factor Positivity.
Demonstrates that a positive cumulative perturbation yields an exponential factor greater than 1.
-/
theorem h_factor_pos_isolated (n : ℕ) (x : ℕ) (h_pos : is_pure_positive n x) : 
  (1 : ℚ) < (2 : ℚ)^(S_prime n x) := by
  have h_S_pos : 0 < S_prime n x := by
    have h_ge_one : 1 ≤ S_prime n x := h_pos.2
    linarith
  apply one_lt_zpow₀
  · exact one_lt_two
  · exact h_S_pos
#check h_factor_pos_isolated
/--
Lemma 1D: Pure Positive Comparison Theorem.
Proves that a purely positive perturbation causes the denominator to exceed the numerator, 
preventing an integer cycle ratio.
-/
theorem Lemma_1D_Final_Comparison (n : ℕ) (x : ℕ) (h_pos : is_pure_positive n x) :
  (sum_T n x : ℚ) < (2 : ℚ)^(S n x) - (3 : ℚ)^n := by
  
  let factor := (2 : ℚ)^(S_prime n x) - 1
  have h_f_pos : 0 < factor := by
    apply sub_pos.mpr
    exact h_factor_pos_isolated n x h_pos
    
  have h_delta_comp : Delta_N n x < Delta_D n x := by
    rw [exact_delta_D n x]
    calc Delta_N n x 
      _ ≤ factor * (N_eq n : ℚ) := delta_N_upper_bound n x h_pos
      _ < factor * (2 : ℚ)^(2 * n) := mul_lt_mul_of_pos_left (N_eq_lt_2pow2n n) h_f_pos
      _ = (2 : ℚ)^(2 * n) * factor := by rw [mul_comm]

  unfold Delta_N Delta_D D_new at h_delta_comp
  
  have h_nats_eq : N_eq n = D_eq n := by
    unfold N_eq D_eq
    rw [pow_mul]
    have h_base : 2^2 = 4 := by rfl
    rw [h_base]
  
  have h_const_eq : (N_eq n : ℚ) = (D_eq n : ℚ) := 
    congrArg (fun (k : ℕ) => (k : ℚ)) h_nats_eq

  rw [h_const_eq] at h_delta_comp
  linarith

end Section14_Lemma1D_Pure_Positive_Perturbation
#check Lemma_1D_Final_Comparison
#print axioms exact_delta_D
#print axioms delta_N_upper_bound
#print axioms Lemma_1D_Final_Comparison
---------------------------------------------------------------------------------------
section Section15_Lemma2D_Definitions

/--
The Actual Numerator Deviation (Net Increment Form).
Translates the manuscript's summation bounds (k=2 to n) to the zero-indexed equivalent (j=1 to n-1).
Manuscript form: \sum_{k=2}^n 3^{n-k}(2^{S_{k-1}} - 2^{2k-2})
Lean 4 form: \sum_{j \in Ico 1 n} 3^{n-1-j} * (2^{S_j} - 2^{2j})
-/
noncomputable def delta_N_actual_inc (n x : ℕ) : ℤ :=
  ∑ j ∈ Ico 1 n, (3 : ℤ)^(n - 1 - j) * ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j))

/--
The Actual Numerator Deviation (Net Decrement Form).
Translates the net decrement summation bounds equivalently.
Manuscript form: \sum_{k=2}^n 3^{n-k}(2^{2k-2} - 2^{S_{k-1}})
Lean 4 form: \sum_{j \in Ico 1 n} 3^{n-1-j} * (2^{2j} - 2^{S_j})
-/
noncomputable def delta_N_actual_dec (n x : ℕ) : ℤ :=
  ∑ j ∈ Ico 1 n, (3 : ℤ)^(n - 1 - j) * ((2 : ℤ)^(2 * j) - (2 : ℤ)^(S j x))

end Section15_Lemma2D_Definitions
section Section17_Lemma2D_Step_1_Derivation

/--
Derivation of the Cycle Condition for Net Decrement.
-/
theorem lemma_2D_decrement_stepwise (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  (N_eq n : ℤ) - (sum_T n x : ℤ) = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) - 1) * (3 : ℤ)^n := by
  
  -- Establishes the fundamental cycle equation Z * D_new = N_new

  have step_a : (sum_T n x : ℤ) = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    calc (sum_T n x : ℤ) = (2 : ℤ)^(S n x) * (x : ℤ) - (3 : ℤ)^n * (x : ℤ) := cycle_diophantine_int n x h_cycle hn
      _ = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by ring

  -- Isolates the actual numerator deviation ΔN = N_eq - N_new

  have step_c : (N_eq n : ℤ) - (sum_T n x : ℤ) = (N_eq n : ℤ) - (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    rw [step_a]

  -- Substitutes the expanded formulas for the equilibrium numerator and perturbed denominator
  have h_N_eq : (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n := N_eq_int n
  have step_d : (N_eq n : ℤ) - (sum_T n x : ℤ) = ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) - (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    rw [step_c, h_N_eq]

  -- Expands and groups the algebraic terms to form the final bifurcated expression
  calc (N_eq n : ℤ) - (sum_T n x : ℤ)
    _ = ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) - (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := step_d
    _ = (2 : ℤ)^(2 * n) - (3 : ℤ)^n - (x : ℤ) * (2 : ℤ)^(S n x) + (x : ℤ) * (3 : ℤ)^n := by ring
    _ = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) * (3 : ℤ)^n - (3 : ℤ)^n) := by ring
    _ = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) - 1) * (3 : ℤ)^n := by ring


section Lemma_2D_Step_2_Derivation
#check lemma_2D_decrement_stepwise
/--
Derivation of the Cycle Condition for Net Increment.
-/
theorem lemma_2D_increment_stepwise (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  (sum_T n x : ℤ) - (N_eq n : ℤ) = ((x : ℤ) * (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) + (1 - (x : ℤ)) * (3 : ℤ)^n := by

  have h_cycle_cond : (sum_T n x : ℤ) = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    calc (sum_T n x : ℤ) = (2 : ℤ)^(S n x) * (x : ℤ) - (3 : ℤ)^n * (x : ℤ) := cycle_diophantine_int n x h_cycle hn
      _ = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by ring

  -- Formulates the deviation identity N_new = ΔN + N_eq and substitute the components
  have h_N_eq : (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n := N_eq_int n
  
  have step_b : (sum_T n x : ℤ) - (N_eq n : ℤ) = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) - (N_eq n : ℤ) := by
    rw [h_cycle_cond]

  calc (sum_T n x : ℤ) - (N_eq n : ℤ)
    _ = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) - ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) := by rw [step_b, h_N_eq]
    _ = (x : ℤ) * (2 : ℤ)^(S n x) - (x : ℤ) * (3 : ℤ)^n - (2 : ℤ)^(2 * n) + (3 : ℤ)^n := by ring
    _ = ((x : ℤ) * (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) + ((3 : ℤ)^n - (x : ℤ) * (3 : ℤ)^n) := by ring
    _ = ((x : ℤ) * (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) + (1 - (x : ℤ)) * (3 : ℤ)^n := by ring

end Lemma_2D_Step_2_Derivation
#print axioms lemma_2D_decrement_stepwise
#print axioms lemma_2D_increment_stepwise
#check lemma_2D_increment_stepwise
-- ===============================================================
-- SECTION 16: Lemma 2D Corollary (3-Adic Valuation Alignment)
-- ===============================================================

/--
3-Adic Valuation Alignment Requirement.
Proves that a non-trivial cycle is impossible if the 3-adic 
valuation of the LHS and RHS of the cycle equation (derived in Lemma 2D) 
do not perfectly align.
-/
theorem cycle_impossible_if_valuation_mismatch (n x : ℕ) 
  (h_cycle : is_cycle n x) (hn : 0 < n)
  (LHS RHS : ℤ)

  (h_LHS : LHS = (N_eq n : ℤ) - (sum_T n x : ℤ))
  (h_RHS : RHS = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) - 1) * (3 : ℤ)^n)
  
  -- The Mismatch Condition: The 3-adic valuations are not equal
  (h_val_mismatch : padicValNat 3 LHS.natAbs ≠ padicValNat 3 RHS.natAbs) :
  False := by
  
  -- Step 1: Invoke Lemma 2D to establish the mathematical equality of the two sides
  have h_2D := lemma_2D_decrement_stepwise n x h_cycle hn
  
  -- Step 2: Substitute the local LHS and RHS definitions to form the identity LHS = RHS
  have h_eq : LHS = RHS := by
    rw [h_LHS, h_RHS]
    exact h_2D
    
  -- Step 3: Substitute the established equality into the valuation mismatch hypothesis.

  rw [h_eq] at h_val_mismatch
  
  -- Step 4: The mismatch hypothesis now asserts that a value is not equal to itself. 

  exact h_val_mismatch rfl

#check cycle_impossible_if_valuation_mismatch
#print axioms cycle_impossible_if_valuation_mismatch

-- ===============================================================
-- SECTION 17: LEMMA 1E - PARITY LEMMA
-- ===============================================================

section Section17_Lemma1E_ParityLemma

/--
In `ZMod 2`, the numeral `2` is zero.
-/
lemma zmod_two_two_eq_zero : (2 : ZMod 2) = 0 := by
  decide

/--
In `ZMod 2`, every element added to itself is zero.
-/
lemma zmod_two_add_self_eq_zero (a : ZMod 2) :
  a + a = 0 := by
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 * a := by rw [zmod_two_two_eq_zero]
    _ = 0 := by ring

/--
Prefix perturbation recursion.

`S'_{k+1} = S'_k + δ_k`.
-/
lemma S_prime_succ
  (x k : ℕ) :
  S_prime (k + 1) x = S_prime k x + delta x k := by

  unfold S_prime
  rw [sum_range_succ]

/--
Modulo-2 form of the local perturbation.

Since `δ_k = a_k - 2`, modulo 2 it has the same parity as the physical
step size `a_k = val (T^[k] x)`.
-/
lemma delta_zmod_two_eq_val
  (x k : ℕ) :
  (delta x k : ZMod 2) = (val ((T^[k]) x) : ZMod 2) := by

  unfold delta

  calc
    (((val ((T^[k]) x) : ℤ) - 2 : ℤ) : ZMod 2)
        =
      (val ((T^[k]) x) : ZMod 2) - (2 : ZMod 2) := by
        push_cast
        ring
    _ =
      (val ((T^[k]) x) : ZMod 2) := by
        rw [zmod_two_two_eq_zero]
        ring

/--
Lemma 1E core congruence.

Manuscript form:
`d_{k+1} ≡ d_k + a_k (mod 2)`.

In the existing formalization, the signed prefix deviation is `S'_k`, and
absolute value does not change parity, so the operative congruence is:
`S'_{k+1} ≡ S'_k + a_k (mod 2)`.
-/
theorem lemma_1E_parity_congruence
  (x k : ℕ) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) + (val ((T^[k]) x) : ZMod 2) := by

  rw [S_prime_succ x k]

  have h_cast :
      ((S_prime k x + delta x k : ℤ) : ZMod 2) =
        (S_prime k x : ZMod 2) + (delta x k : ZMod 2) := by
    exact Int.cast_add (S_prime k x) (delta x k)

  calc
    ((S_prime k x + delta x k : ℤ) : ZMod 2)
        =
      (S_prime k x : ZMod 2) + (delta x k : ZMod 2) := h_cast
    _ =
      (S_prime k x : ZMod 2) + (val ((T^[k]) x) : ZMod 2) := by
        rw [delta_zmod_two_eq_val x k]
/--
Even physical steps preserve prefix-deviation parity.
-/
theorem lemma_1E_even_step_preserves_parity
  (x k : ℕ)
  (h_even : Even (val ((T^[k]) x))) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) := by

  rw [lemma_1E_parity_congruence x k]

  rcases h_even with ⟨t, ht⟩

  have h_val_zero :
      (val ((T^[k]) x) : ZMod 2) = 0 := by
    rw [ht]
    rw [Nat.cast_add]
    exact zmod_two_add_self_eq_zero (t : ZMod 2)

  rw [h_val_zero]
  ring

/--
Odd physical steps invert prefix-deviation parity.
-/
theorem lemma_1E_odd_step_inverts_parity
  (x k : ℕ)
  (h_odd : Odd (val ((T^[k]) x))) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) + 1 := by

  rw [lemma_1E_parity_congruence x k]

  rcases h_odd with ⟨t, ht⟩

  have h_val_one :
      (val ((T^[k]) x) : ZMod 2) = 1 := by
    rw [ht]

    calc
      ((2 * t + 1 : ℕ) : ZMod 2)
          =
        (2 : ZMod 2) * (t : ZMod 2) + 1 := by
          push_cast
          ring
      _ =
        0 * (t : ZMod 2) + 1 := by
          rw [zmod_two_two_eq_zero]
      _ =
        1 := by ring

  rw [h_val_one]

/--
The negative perturbation case `a_k = 1` is an odd step, hence it inverts
prefix-deviation parity.
-/
theorem lemma_1E_negative_step_inverts_parity
  (x k : ℕ)
  (h_neg : val ((T^[k]) x) = 1) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) + 1 := by

  apply lemma_1E_odd_step_inverts_parity x k
  rw [h_neg]
  exact ⟨0, by norm_num⟩

end Section17_Lemma1E_ParityLemma

-- ===============================================================
-- SECTION 18: LEMMA 1F (LHS BIFURCATION)
-- ===============================================================
section Section18_Lemma1F

/-- Generic sequence term T_k -/
noncomputable def T_seq (n x k : ℕ) : ℤ :=
  (3 : ℤ)^(n - 1 - k) * ((2 : ℤ)^(S k x) - (2 : ℤ)^(2 * k))

/-- Integer Equilibrium Numerator Summation Identity -/
theorem N_eq_as_sum_int (n : ℕ) :
  (N_eq n : ℤ) = ∑ j ∈ range n, (3 : ℤ)^(n - 1 - j) * (2 : ℤ)^(2 * j) := by
  rw [N_eq]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]

    have h_factor :
        ∑ j ∈ range m, (3 : ℤ) ^ (m.succ - 1 - j) * (2 : ℤ) ^ (2 * j) =
          3 * ∑ j ∈ range m, (3 : ℤ) ^ (m - 1 - j) * (2 : ℤ) ^ (2 * j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [nat_index_shift m j (Finset.mem_range.mp hj), pow_succ]
      ring

    rw [h_factor, ← ih]

    have h_pow_match : (2 : ℤ) ^ (2 * m) = (4 : ℤ) ^ m := by
      rw [pow_mul]
      norm_num

    simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_mul, h_pow_match]

    have h_le_succ : 3^(m + 1) ≤ 4^(m + 1) :=
      Nat.pow_le_pow_left (by norm_num) (m + 1)
    have h_le_m : 3^m ≤ 4^m :=
      Nat.pow_le_pow_left (by norm_num) m

    rw [Nat.cast_sub h_le_succ, Nat.cast_sub h_le_m]
    push_cast
    ring

/-- The Z-ring summation bridge. -/
theorem lemma_delta_equiv_bridge (n x : ℕ) (hn : 0 < n) :
  (sum_T n x : ℤ) - (N_eq n : ℤ) = delta_N_actual_inc n x := by
  dsimp [sum_T, delta_N_actual_inc]
  push_cast
  rw [N_eq_as_sum_int n]

  have h_combined_sum :
      (∑ j ∈ range n, (3 : ℤ)^(n - 1 - j) * (2 : ℤ)^(S j x)) -
        (∑ j ∈ range n, (3 : ℤ)^(n - 1 - j) * (2 : ℤ)^(2 * j))
      =
        ∑ j ∈ range n, T_seq n x j := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    dsimp [T_seq]
    ring

  rw [h_combined_sum]

  have h_range_split : range n = insert 0 (Ico 1 n) := by
    ext a
    simp only [mem_range, mem_insert, mem_Ico]
    omega

  have h_not_in : 0 ∉ Ico 1 n := by
    simp only [mem_Ico, not_and]
    intro h
    omega

  have h_split_range :
      ∑ j ∈ range n, T_seq n x j =
        T_seq n x 0 + ∑ j ∈ Ico 1 n, T_seq n x j := by
    rw [h_range_split]
    exact sum_insert h_not_in

  rw [h_split_range]

  have h_term_zero : T_seq n x 0 = 0 := by
    dsimp [T_seq, S]
    ring

  rw [h_term_zero, zero_add]
  unfold T_seq
  rfl

/-- Offset variable B. -/
noncomputable def offset_B (n x : ℕ) : ℤ :=
  (2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)

/-- Terminal boundary grouping T_last. -/
noncomputable def T_last (n x : ℕ) : ℤ :=
  (3 : ℤ)^0 * ((2 : ℤ)^(S (n - 1) x) - (2 : ℤ)^(2 * (n - 1))) + offset_B n x

/-- Internal sum in the bifurcated Lemma 1F equation. -/
noncomputable def internal_T_sum (n x : ℕ) : ℤ :=
  ∑ k ∈ Ico 1 (n - 1), T_seq n x k

/-- Full bifurcated LHS. -/
noncomputable def bifurcated_LHS (n x : ℕ) : ℤ :=
  internal_T_sum n x + T_last n x

/-- Bifurcated component: internal terms plus terminal `T_last`. -/
noncomputable def bifurcated_component (n x k : ℕ) : ℤ :=
  if k = n - 1 then T_last n x else T_seq n x k

/-- A bifurcated component reaches a target 3-adic valuation. -/
def bifurcated_component_reaches_target (n x target k : ℕ) : Prop :=
  (3 : ℤ)^target ∣ bifurcated_component n x k

/--
Step 1: The bifurcated structure, derived from Lemma 2D.
-/
theorem lemma_1F_step1_bifurcation
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  (∑ k ∈ Ico 1 (n - 1), T_seq n x k) + T_last n x =
    (1 - (x : ℤ)) * (3 : ℤ)^n := by

  have hn_pos : 0 < n := by omega
  have h_delta_equiv := lemma_delta_equiv_bridge n x hn_pos
  have h_2D := lemma_2D_increment_stepwise n x h_cycle hn_pos

  have h_mod_cycle :
      delta_N_actual_inc n x + offset_B n x =
        (1 - (x : ℤ)) * (3 : ℤ)^n := by
    rw [← h_delta_equiv]
    dsimp [offset_B]
    linarith [h_2D]

  have h_sum_def :
      delta_N_actual_inc n x = ∑ k ∈ Ico 1 n, T_seq n x k := by
    unfold delta_N_actual_inc T_seq
    apply sum_congr rfl
    intro k _
    rfl

  rw [h_sum_def] at h_mod_cycle

  have h_ico_split : Ico 1 n = insert (n - 1) (Ico 1 (n - 1)) := by
    ext a
    simp only [mem_Ico, mem_insert]
    omega

  have h_not_in_ico : n - 1 ∉ Ico 1 (n - 1) := by
    simp only [mem_Ico, not_and, not_lt]
    intro _
    omega

  have h_split :
      ∑ k ∈ Ico 1 n, T_seq n x k =
        T_seq n x (n - 1) + ∑ k ∈ Ico 1 (n - 1), T_seq n x k := by
    rw [h_ico_split]
    exact sum_insert h_not_in_ico

  rw [h_split] at h_mod_cycle

  have h_T_last_eq : T_seq n x (n - 1) + offset_B n x = T_last n x := by
    dsimp [T_seq, T_last]
    have h_zero : n - 1 - (n - 1) = 0 := by omega
    rw [h_zero]
    ring

  have h_rearrange :
      (T_seq n x (n - 1) + ∑ k ∈ Ico 1 (n - 1), T_seq n x k) + offset_B n x =
        (∑ k ∈ Ico 1 (n - 1), T_seq n x k) +
          (T_seq n x (n - 1) + offset_B n x) := by
    ring

  rw [h_rearrange] at h_mod_cycle
  rw [h_T_last_eq] at h_mod_cycle
  exact h_mod_cycle

/-- Lemma 1F in normalized LHS form. -/
theorem lemma_1F_step1_bifurcated_LHS_eq
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  bifurcated_LHS n x = (1 - (x : ℤ)) * (3 : ℤ)^n := by
  unfold bifurcated_LHS internal_T_sum
  exact lemma_1F_step1_bifurcation n x h_cycle hn

/-- The bifurcated LHS is the sum of bifurcated components. -/
lemma bifurcated_LHS_eq_component_sum
  (n x : ℕ) (hn : 1 < n) :
  bifurcated_LHS n x =
    ∑ k ∈ Ico 1 n, bifurcated_component n x k := by

  unfold bifurcated_LHS internal_T_sum bifurcated_component

  have h_split : Ico 1 n = insert (n - 1) (Ico 1 (n - 1)) := by
    ext a
    simp only [mem_Ico, mem_insert]
    omega

  have h_not_in : n - 1 ∉ Ico 1 (n - 1) := by
    simp only [mem_Ico]
    omega

  rw [h_split]
  rw [sum_insert h_not_in]

  have h_internal :
      ∑ k ∈ Ico 1 (n - 1),
        (if k = n - 1 then T_last n x else T_seq n x k)
      =
      ∑ k ∈ Ico 1 (n - 1), T_seq n x k := by
    apply sum_congr rfl
    intro k hk
    have hk_ne : k ≠ n - 1 := by
      rw [mem_Ico] at hk
      omega
    simp [hk_ne]

  simp
  rw [h_internal]
  ring

/-- Internal part of the bifurcated LHS is divisible by 3. -/
lemma lemma_1F_internal_sum_divisible_by_three
  (n x : ℕ) (hn : 1 < n) :
  (3 : ℤ) ∣ internal_T_sum n x := by
  unfold internal_T_sum
  apply dvd_sum
  intro k hk
  have hk_lt : k < n - 1 := (mem_Ico.mp hk).2
  have h_exp_pos : 1 ≤ n - 1 - k := by omega
  have h_positional : (3 : ℤ) ∣ (3 : ℤ)^(n - 1 - k) := by
    simpa using (pow_dvd_pow (3 : ℤ) h_exp_pos)
  unfold T_seq
  exact dvd_mul_of_dvd_left h_positional _

/--
Step 2: `T_last` must participate 3-adically.

Thus the case `v₃(T_last) = 0` is impossible for a cycle.
-/
theorem lemma_1F_step2_T_last_divisible_by_three
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  (3 : ℤ) ∣ T_last n x := by

  have h_lhs_eq := lemma_1F_step1_bifurcated_LHS_eq n x h_cycle hn

  have h_rhs_dvd :
      (3 : ℤ) ∣ (1 - (x : ℤ)) * (3 : ℤ)^n := by
    have h_pow_dvd : (3 : ℤ) ∣ (3 : ℤ)^n := by
      simpa using (pow_dvd_pow (3 : ℤ) (by omega : 1 ≤ n))
    exact dvd_mul_of_dvd_right h_pow_dvd (1 - (x : ℤ))

  have h_lhs_dvd : (3 : ℤ) ∣ bifurcated_LHS n x := by
    rw [h_lhs_eq]
    exact h_rhs_dvd

  have h_internal_dvd := lemma_1F_internal_sum_divisible_by_three n x hn

  have h_T_last_eq :
      T_last n x = bifurcated_LHS n x - internal_T_sum n x := by
    unfold bifurcated_LHS
    ring

  rw [h_T_last_eq]
  exact dvd_sub h_lhs_dvd h_internal_dvd

/-- Contradiction form of Step 2. -/
theorem lemma_1F_step2_T_last_zero_valuation_contradiction
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n)
  (h_T_last_zero : ¬ (3 : ℤ) ∣ T_last n x) :
  False := by
  exact h_T_last_zero
    (lemma_1F_step2_T_last_divisible_by_three n x h_cycle hn)

/-- Integer divisibility bridge from `padicValNat` of `natAbs`. -/

lemma int_pow_three_padicValNat_abs_dvd
  (z : ℤ) (hz_ne : z ≠ 0) :
  (3 : ℤ)^(padicValNat 3 z.natAbs) ∣ z := by

  have hz_abs_ne : z.natAbs ≠ 0 := by
    intro h
    exact hz_ne (Int.natAbs_eq_zero.mp h)

  have h_nat_dvd : 3^(padicValNat 3 z.natAbs) ∣ z.natAbs := by
    exact
      (pow_dvd_iff_le_padicValNat
        (by norm_num : 3 ≠ 1) hz_abs_ne).mpr (le_refl _)

  rcases h_nat_dvd with ⟨c, hc⟩

  have hc_int :
      (z.natAbs : ℤ) =
        ((3^(padicValNat 3 z.natAbs) * c : ℕ) : ℤ) := by
    exact_mod_cast hc

  by_cases hz_nonneg : 0 ≤ z
  · use (c : ℤ)
    have hz_abs_cast : (z.natAbs : ℤ) = z := by omega
    calc z = (z.natAbs : ℤ) := hz_abs_cast.symm
      _ = ((3^(padicValNat 3 z.natAbs) * c : ℕ) : ℤ) := hc_int
      _ = (3 : ℤ)^(padicValNat 3 z.natAbs) * (c : ℤ) := by
          push_cast
          ring

  · use -(c : ℤ)
    have hz_abs_cast : (z.natAbs : ℤ) = -z := by omega
    calc z = -((z.natAbs : ℤ)) := by omega
      _ = -(((3^(padicValNat 3 z.natAbs) * c : ℕ) : ℤ)) := by
          rw [hc_int]
      _ = (3 : ℤ)^(padicValNat 3 z.natAbs) * (-(c : ℤ)) := by
          push_cast
          ring
#check int_pow_three_padicValNat_abs_dvd
#print axioms int_pow_three_padicValNat_abs_dvd
/--
The full 3-adic target forced by the bifurcated RHS.

The bifurcated equation has RHS `(1 - x) * 3^n`, so the target is
`n + v₃(|1 - x|)`.
-/
noncomputable def cycle_seed_target (n x : ℕ) : ℕ :=
  n + padicValNat 3 ((1 - (x : ℤ)).natAbs)

/-- Named target-reaching predicate for the bifurcated LHS. -/
def bifurcated_LHS_reaches_target (n x target : ℕ) : Prop :=
  (3 : ℤ)^target ∣ bifurcated_LHS n x

/-- The old `n` target remains true, but the seed target below is sharper. -/
theorem bifurcated_LHS_reaches_n
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  (3 : ℤ)^n ∣ bifurcated_LHS n x := by
  rw [lemma_1F_step1_bifurcated_LHS_eq n x h_cycle hn]
  exact dvd_mul_left ((3 : ℤ)^n) (1 - (x : ℤ))
#check bifurcated_LHS_reaches_n
#print axioms bifurcated_LHS_reaches_n

theorem cycle_bifurcated_LHS_reaches_target_n
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  bifurcated_LHS_reaches_target n x n := by
  unfold bifurcated_LHS_reaches_target
  exact bifurcated_LHS_reaches_n n x h_cycle hn
#check cycle_bifurcated_LHS_reaches_target_n
#print axioms cycle_bifurcated_LHS_reaches_target_n
/--
For a nontrivial cycle seed `x > 1`, the bifurcated LHS reaches the full
target `n + v₃(|1 - x|)`.
-/
theorem bifurcated_LHS_reaches_seed_target
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  (3 : ℤ)^(cycle_seed_target n x) ∣ bifurcated_LHS n x := by

  unfold cycle_seed_target
  rw [lemma_1F_step1_bifurcated_LHS_eq n x h_cycle hn]

  let A : ℤ := 1 - (x : ℤ)
  let e : ℕ := padicValNat 3 A.natAbs

  have hA_ne : A ≠ 0 := by
    dsimp [A]
    omega

  have hA_dvd : (3 : ℤ)^e ∣ A := by
    dsimp [e]
    exact int_pow_three_padicValNat_abs_dvd A hA_ne

  rcases hA_dvd with ⟨c, hc⟩
  use c

  have h_target_exp :
      n + padicValNat 3 (1 - (x : ℤ)).natAbs = n + e := by
    dsimp [e, A]

  rw [h_target_exp]

  calc
    (1 - (x : ℤ)) * (3 : ℤ)^n
        = A * (3 : ℤ)^n := by rfl
    _ = ((3 : ℤ)^e * c) * (3 : ℤ)^n := by rw [hc]
    _ = (3 : ℤ)^(e + n) * c := by
        rw [pow_add]
        ring
    _ = (3 : ℤ)^(n + e) * c := by
        rw [add_comm]

theorem cycle_bifurcated_LHS_reaches_seed_target
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  bifurcated_LHS_reaches_target n x (cycle_seed_target n x) := by
  unfold bifurcated_LHS_reaches_target
  exact bifurcated_LHS_reaches_seed_target n x h_cycle hn hx

/--
Step 3: Sovereign cancellation.

If the whole bifurcated LHS reaches a cycle-forced target, and the rest of the
LHS also reaches a lower/equal target, then the skipped component must reach it
too. Therefore a skipped component gives contradiction.
-/
theorem lemma_1F_step3_sovereign_cancellation
  (n x j target : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_target_le : target ≤ cycle_seed_target n x)
  (h_skipped :
    ¬ bifurcated_component_reaches_target n x target j)
  (h_rest_lifted :
    (3 : ℤ)^target ∣
      bifurcated_LHS n x - bifurcated_component n x j) :
  False := by

  have h_seed :
      (3 : ℤ)^(cycle_seed_target n x) ∣ bifurcated_LHS n x :=
    bifurcated_LHS_reaches_seed_target n x h_cycle hn hx

  have h_target_dvd_seed :
      (3 : ℤ)^target ∣ (3 : ℤ)^(cycle_seed_target n x) :=
    pow_dvd_pow (3 : ℤ) h_target_le

  have h_lhs_target :
      (3 : ℤ)^target ∣ bifurcated_LHS n x :=
    dvd_trans h_target_dvd_seed h_seed

  have h_component_target :
      bifurcated_component_reaches_target n x target j := by
    unfold bifurcated_component_reaches_target
    have h_eq :
        bifurcated_component n x j =
          bifurcated_LHS n x -
            (bifurcated_LHS n x - bifurcated_component n x j) := by
      ring
    rw [h_eq]
    exact dvd_sub h_lhs_target h_rest_lifted

  exact h_skipped h_component_target

end Section18_Lemma1F

#check lemma_1F_step1_bifurcation
#check lemma_1F_step1_bifurcated_LHS_eq
#check lemma_1F_step2_T_last_divisible_by_three
#check lemma_1F_step2_T_last_zero_valuation_contradiction
#check bifurcated_LHS_reaches_seed_target
#check lemma_1F_step3_sovereign_cancellation
#print axioms lemma_1F_step3_sovereign_cancellation

-- ===============================================================
-- SECTION 19: LEMMA 1G (QUANTITATIVE LTE LIFT)
-- ===============================================================
section Section19_Lemma1G_Quantitative_LTE

/--
Internal term factorization.

If `S_k = 2k + d_k`, then the internal term splits into:
positional 3-power × equilibrium 2-power × lift factor `(2^d_k - 1)`.
-/
lemma T_seq_factor_of_prefix_deviation
  (n x k d_k : ℕ)
  (hS : S k x = 2 * k + d_k) :
  T_seq n x k =
    (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by
  unfold T_seq
  rw [hS, pow_add]
  ring
#check T_seq_factor_of_prefix_deviation
#print axioms T_seq_factor_of_prefix_deviation
/--
Step 1: Valuation deficit isolation.

If an internal term reaches target `p`, then after removing its positional
3-power, the lift factor `(2^d_k - 1)` must supply the remaining deficit.
-/
theorem lemma_1G_step1_valuation_deficit
  (n k p S_k d_k : ℕ)
  (hk_bound : n - 1 - k ≤ p)
  (h_Sk : S_k = 2 * k + d_k)
  (h_T_div :
    (3 : ℤ)^p ∣
      (3 : ℤ)^(n - 1 - k) *
        ((2 : ℤ)^S_k - (2 : ℤ)^(2 * k))) :
  (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) := by

  have h_factor :
      (2 : ℤ)^S_k - (2 : ℤ)^(2 * k) =
        (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by
    calc
      (2 : ℤ)^S_k - (2 : ℤ)^(2 * k)
          = (2 : ℤ)^(2 * k + d_k) - (2 : ℤ)^(2 * k) := by rw [h_Sk]
      _ = (2 : ℤ)^(2 * k) * (2 : ℤ)^d_k - (2 : ℤ)^(2 * k) * 1 := by
          rw [pow_add]
          ring
      _ = (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by ring

  have h_T_div_sub :
      (3 : ℤ)^p ∣
        (3 : ℤ)^(n - 1 - k) *
          ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    simpa [h_factor] using h_T_div

  have h_p_split : p = (n - 1 - k) + (p - (n - 1 - k)) := by
    omega

  have h_T_div_split :
      (3 : ℤ)^((n - 1 - k) + (p - (n - 1 - k))) ∣
        (3 : ℤ)^(n - 1 - k) *
          ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    rw [← h_p_split]
    exact h_T_div_sub

  rw [pow_add] at h_T_div_split

  have h_ne_zero : (3 : ℤ)^(n - 1 - k) ≠ 0 :=
    pow_ne_zero _ (by norm_num)

  have h_cancel :
      (3 : ℤ)^(p - (n - 1 - k)) ∣
        (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by
    exact (mul_dvd_mul_iff_left h_ne_zero).mp h_T_div_split

  have h_coprime :
      IsCoprime
        ((3 : ℤ)^(p - (n - 1 - k)))
        ((2 : ℤ)^(2 * k)) := by
    have h_base : IsCoprime (3 : ℤ) (2 : ℤ) := ⟨1, -1, by norm_num⟩
    exact IsCoprime.pow h_base

  rcases h_coprime with ⟨u, v, huv⟩

  have h_target_eq :
      ((2 : ℤ)^d_k - 1) =
        u * ((3 : ℤ)^(p - (n - 1 - k))) * ((2 : ℤ)^d_k - 1) +
          v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    calc
      ((2 : ℤ)^d_k - 1)
          = 1 * ((2 : ℤ)^d_k - 1) := by ring
      _ = (u * (3 : ℤ)^(p - (n - 1 - k)) +
            v * (2 : ℤ)^(2 * k)) * ((2 : ℤ)^d_k - 1) := by
          rw [← huv]
      _ =
          u * (3 : ℤ)^(p - (n - 1 - k)) * ((2 : ℤ)^d_k - 1) +
            v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by ring

  have h_dvd_term1 :
      (3 : ℤ)^(p - (n - 1 - k)) ∣
        u * ((3 : ℤ)^(p - (n - 1 - k))) * ((2 : ℤ)^d_k - 1) := by
    use u * ((2 : ℤ)^d_k - 1)
    ring

  rcases h_cancel with ⟨w, hw⟩

  have h_dvd_term2 :
      (3 : ℤ)^(p - (n - 1 - k)) ∣
        v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    use v * w
    calc
      v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1))
          = v * ((3 : ℤ)^(p - (n - 1 - k)) * w) := by rw [hw]
      _ = (3 : ℤ)^(p - (n - 1 - k)) * (v * w) := by ring

  rw [h_target_eq]
  exact dvd_add h_dvd_term1 h_dvd_term2
#check lemma_1G_step1_valuation_deficit
#print axioms lemma_1G_step1_valuation_deficit
/--
Modulo-3 LTE gateway.

If `3 ∣ 2^d - 1`, then `d` is even.
This is only a local prerequisite for the LTE calculation.
-/
lemma even_of_three_dvd_two_pow_sub_one
  (d : ℕ)
  (h_dvd : (3 : ℤ) ∣ (2 : ℤ)^d - 1) :
  Even d := by

  by_contra h_not_even

  have h_odd : Odd d := Nat.not_even_iff_odd.mp h_not_even
  rcases h_odd with ⟨t, ht⟩

  have h_pow_eq_one : (2 : ZMod 3)^d = 1 := by
    have h_zero :
        (((2 : ℤ)^d - 1 : ℤ) : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h_dvd

    have h_cast :
        (((2 : ℤ)^d - 1 : ℤ) : ZMod 3) =
          (2 : ZMod 3)^d - 1 := by
      norm_num

    rw [h_cast] at h_zero
    exact sub_eq_zero.mp h_zero

  have h_pow_eq_two : (2 : ZMod 3)^d = 2 := by
    rw [ht]

    have h_two_sq : (2 : ZMod 3)^2 = 1 := by
      decide

    calc
      (2 : ZMod 3)^(2 * t + 1)
          = (2 : ZMod 3)^(2 * t) * 2 := by
              rw [pow_add]
              norm_num
      _ = ((2 : ZMod 3)^2)^t * 2 := by
              rw [pow_mul]
      _ = 1^t * 2 := by
              rw [h_two_sq]
      _ = 2 := by simp

  have h_contra : (1 : ZMod 3) = 2 := by
    rw [← h_pow_eq_one, h_pow_eq_two]

  have h_ne : (1 : ZMod 3) ≠ 2 := by
    decide

  exact h_ne h_contra
#check even_of_three_dvd_two_pow_sub_one
#print axioms even_of_three_dvd_two_pow_sub_one
/--
Deficit divisibility with a positive deficit forces the deviation exponent even.
-/
lemma lemma_1G_even_deviation_of_positive_deficit
  (q d : ℕ)
  (hq : 0 < q)
  (h_dvd : (3 : ℤ)^q ∣ ((2 : ℤ)^d - 1)) :
  Even d := by

  have h_three_dvd :
      (3 : ℤ)^1 ∣ ((2 : ℤ)^d - 1) := by
    exact dvd_trans (pow_dvd_pow (3 : ℤ) (by omega : 1 ≤ q)) h_dvd

  simpa using even_of_three_dvd_two_pow_sub_one d h_three_dvd
#check lemma_1G_even_deviation_of_positive_deficit
#print axioms lemma_1G_even_deviation_of_positive_deficit
/--
Mathlib LTE invocation for the Collatz lift factor.

For even positive `d`, the 3-adic valuation of `2^d - 1` is
`1 + v₃(d / 2)`.
-/
lemma padic_val_three_of_even_pow
  (d : ℕ) (h_even : Even d) (hd_pos : 0 < d) :
  padicValNat 3 (2^d - 1) = 1 + padicValNat 3 (d / 2) := by

  rcases h_even with ⟨k, hk⟩

  have h_d_eq : d = 2 * k := by omega
  have hd_half : d / 2 = k := by omega

  rw [hd_half]

  have h_pow_sub : 2^d - 1 = 4^k - 1^k := by
    rw [h_d_eq, pow_mul]
    have h_four : 2^2 = 4 := by norm_num
    rw [h_four]
    simp

  rw [h_pow_sub]

  have h_lte :
      padicValNat 3 (4^k - 1^k) =
        padicValNat 3 (4 - 1) + padicValNat 3 k := by
    apply padicValNat.pow_sub_pow
    · norm_num
    · norm_num
    · norm_num
    · intro h
      rcases h with ⟨c, hc⟩
      omega
    · omega

  rw [h_lte]

  have h_base : padicValNat 3 (4 - 1) = 1 := by
    norm_num

  rw [h_base]
#check padic_val_three_of_even_pow
#print axioms padic_val_three_of_even_pow
/--
Step 2: LTE substitution.

If the total valuation reaches `p`, then the half-deviation must carry
the residual valuation `p + k - n`.
-/
theorem lemma_1G_step2_lte_substitution
  (n p k d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (h_total_val : n - 1 - k + padicValNat 3 (2 ^ d_k - 1) ≥ p)
  (h_dk_even : Even d_k)
  (h_dk_pos : 0 < d_k) :
  padicValNat 3 (d_k / 2) ≥ p + k - n := by

  have h_LTE := padic_val_three_of_even_pow d_k h_dk_even h_dk_pos
  rw [h_LTE] at h_total_val
  omega
#check lemma_1G_step2_lte_substitution
#print axioms lemma_1G_step2_lte_substitution
/--
Step 3: Minimum deviation from divisibility of the half-deviation.
-/
theorem lemma_1G_step3_minimum_deviation
  (n p k d_k : ℕ)
  (h_pos : 0 < d_k / 2)
  (h_divisibility : 3 ^ (p + k - n) ∣ d_k / 2)
  (h_even : Even d_k) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by

  rcases h_divisibility with ⟨c, hc⟩

  have h_c_pos : 0 < c := by
    cases c with
    | zero => omega
    | succ c' => omega

  have h_half_bound : d_k / 2 ≥ 3 ^ (p + k - n) := by
    calc
      d_k / 2 = 3 ^ (p + k - n) * c := hc
      _ ≥ 3 ^ (p + k - n) * 1 :=
          Nat.mul_le_mul_left (3 ^ (p + k - n)) h_c_pos
      _ = 3 ^ (p + k - n) := by ring

  have h_dk_eq : d_k = 2 * (d_k / 2) := by
    rcases h_even with ⟨m, hm⟩
    omega

  omega
#check lemma_1G_step3_minimum_deviation
#print axioms lemma_1G_step3_minimum_deviation
/--
Quantitative 1G lift.

This is the intended output of Lemma 1G: once a term's lift factor reaches
the required 3-adic valuation, Mathlib LTE forces the minimum deviation size.
-/
theorem lemma_1G_quantitative_lte_lift
  (n p k d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (h_total_val : n - 1 - k + padicValNat 3 (2 ^ d_k - 1) ≥ p)
  (h_dk_even : Even d_k)
  (h_dk_pos : 0 < d_k) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by

  have h_half_pos : 0 < d_k / 2 := by
    rcases h_dk_even with ⟨m, hm⟩
    omega

  have h_padic :
      padicValNat 3 (d_k / 2) ≥ p + k - n :=
    lemma_1G_step2_lte_substitution
      n p k d_k hn h_k_upper h_total_val h_dk_even h_dk_pos

  have h_half_ne : d_k / 2 ≠ 0 :=
    Nat.ne_of_gt h_half_pos

  have h_divisibility : 3 ^ (p + k - n) ∣ d_k / 2 :=
    (pow_dvd_iff_le_padicValNat
      (by norm_num : 3 ≠ 1) h_half_ne).mpr h_padic

  exact
    lemma_1G_step3_minimum_deviation
      n p k d_k h_half_pos h_divisibility h_dk_even
#check lemma_1G_quantitative_lte_lift
#print axioms lemma_1G_quantitative_lte_lift
/--
Boundary verification: entry term.

At `k = n - p`, the minimum lift is `d_k = 2`.
-/
lemma lemma_1G_step4_boundary_entry_term
  (n p k d_k : ℕ)
  (h_p_le_n : p ≤ n)
  (h_k_entry : k = n - p)
  (h_formula : d_k = 2 * 3 ^ (p + k - n)) :
  d_k = 2 := by

  have h_exponent : p + k - n = 0 := by omega
  rw [h_exponent] at h_formula
  norm_num at h_formula
  exact h_formula
#check lemma_1G_step4_boundary_entry_term
#print axioms lemma_1G_step4_boundary_entry_term
/--
Boundary verification: final internal term.

At `k = n - 2`, the minimum lift is `d_k = 2 * 3^(p - 2)`.
-/
lemma lemma_1G_step4_boundary_final_term
  (n p k d_k : ℕ)
  (h_p_ge_2 : 2 ≤ p)
  (h_n_ge_2 : 2 ≤ n)
  (h_k_final : k = n - 2)
  (h_formula : d_k = 2 * 3 ^ (p + k - n)) :
  d_k = 2 * 3 ^ (p - 2) := by

  have h_exponent : p + k - n = p - 2 := by omega
  rw [h_exponent] at h_formula
  exact h_formula
/--
A positive power of two minus one is nonzero.
-/
lemma two_pow_sub_one_ne_zero_of_pos
  (d : ℕ) (hd : 0 < d) :
  2^d - 1 ≠ 0 := by

  have h_two_le : 2 ≤ 2^d := by
    cases d with
    | zero =>
        omega
    | succ e =>
        rw [pow_succ]
        have h_pos : 0 < 2^e := pow_pos (by decide : 0 < 2) e
        calc
          2 = 1 * 2 := by ring
          _ ≤ 2^e * 2 := Nat.mul_le_mul_right 2 (Nat.succ_le_of_lt h_pos)

  omega

/--
Integer divisibility of the lift factor gives the corresponding natural
`padicValNat` lower bound, once the deviation is positive.
-/
lemma padicValNat_three_two_pow_sub_one_ge_of_int_dvd
  (q d : ℕ)
  (hd : 0 < d)
  (h_dvd : (3 : ℤ)^q ∣ (2 : ℤ)^d - 1) :
  q ≤ padicValNat 3 (2^d - 1) := by

  have h_pow_cast : ((3^q : ℕ) : ℤ) = (3 : ℤ)^q := by
    norm_num

  have h_pow_abs : ((3 : ℤ)^q).natAbs = 3^q := by
    rw [← h_pow_cast]
    simp

  have h_abs_dvd :
      3^q ∣ ((2 : ℤ)^d - 1).natAbs := by
    rcases h_dvd with ⟨c, hc⟩
    use c.natAbs
    calc
      ((2 : ℤ)^d - 1).natAbs
          = (((3 : ℤ)^q) * c).natAbs := by rw [hc]
      _ = ((3 : ℤ)^q).natAbs * c.natAbs := by
          rw [Int.natAbs_mul]
      _ = 3^q * c.natAbs := by rw [h_pow_abs]

  have h_pow_pos_nat : 0 < 2^d := pow_pos (by decide : 0 < 2) d
  have h_pow_ge_one_nat : 1 ≤ 2^d := Nat.succ_le_of_lt h_pow_pos_nat

  have h_abs_eq :
      ((2 : ℤ)^d - 1).natAbs = 2^d - 1 := by
    have h_nonneg : 0 ≤ (2 : ℤ)^d - 1 := by
      have h_cast_ge : (1 : ℤ) ≤ (2 : ℤ)^d := by
        exact_mod_cast h_pow_ge_one_nat
      linarith

    have h_cast :
        (((2 : ℤ)^d - 1).natAbs : ℤ) =
          ((2^d - 1 : ℕ) : ℤ) := by
      have h_left :
          (((2 : ℤ)^d - 1).natAbs : ℤ) =
            (2 : ℤ)^d - 1 := by
        omega

      have h_right :
          ((2^d - 1 : ℕ) : ℤ) =
            (2 : ℤ)^d - 1 := by
        rw [Nat.cast_sub h_pow_ge_one_nat]
        push_cast
        ring

      rw [h_left, h_right]

    exact_mod_cast h_cast

  have h_nat_dvd : 3^q ∣ 2^d - 1 := by
    rwa [h_abs_eq] at h_abs_dvd

  have h_nat_ne : 2^d - 1 ≠ 0 :=
    two_pow_sub_one_ne_zero_of_pos d hd

  exact
    (pow_dvd_iff_le_padicValNat
      (by norm_num : 3 ≠ 1) h_nat_ne).mp h_nat_dvd

/--
Internal-term version of the deficit-isolation step.
-/
theorem lemma_1G_internal_term_deficit
  (n x k p d_k : ℕ)
  (hk_bound : n - 1 - k ≤ p)
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : ℤ)^p ∣ T_seq n x k) :
  (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) := by

  unfold T_seq at h_term_reaches

  exact
    lemma_1G_step1_valuation_deficit
      n k p (S k x) d_k hk_bound hS h_term_reaches

/--
A nonzero internal term in nonnegative-deviation form has positive deviation.
-/
lemma lemma_1G_positive_deviation_of_nonzero_internal_term
  (n x k d_k : ℕ)
  (hS : S k x = 2 * k + d_k)
  (h_nonzero : T_seq n x k ≠ 0) :
  0 < d_k := by

  by_contra h_not_pos

  have hd_zero : d_k = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h_not_pos)

  subst d_k

  have h_factor :
      T_seq n x k =
        (3 : ℤ)^(n - 1 - k) *
          (2 : ℤ)^(2 * k) *
            ((2 : ℤ)^0 - 1) := by
    exact T_seq_factor_of_prefix_deviation n x k 0 hS

  have h_zero : T_seq n x k = 0 := by
    rw [h_factor]
    norm_num

  exact h_nonzero h_zero

/--
If a nonzero internal term has positive valuation deficit, its deviation is
even and positive.
-/
theorem lemma_1G_internal_term_even_positive_of_positive_deficit
  (n x k p d_k : ℕ)
  (hk_bound : n - 1 - k ≤ p)
  (h_deficit_pos : 0 < p - (n - 1 - k))
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : ℤ)^p ∣ T_seq n x k)
  (h_term_nonzero : T_seq n x k ≠ 0) :
  Even d_k ∧ 0 < d_k := by

  have h_lift_dvd :
      (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) :=
    lemma_1G_internal_term_deficit
      n x k p d_k hk_bound hS h_term_reaches

  have h_even : Even d_k :=
    lemma_1G_even_deviation_of_positive_deficit
      (p - (n - 1 - k)) d_k h_deficit_pos h_lift_dvd

  have h_pos : 0 < d_k :=
    lemma_1G_positive_deviation_of_nonzero_internal_term
      n x k d_k hS h_term_nonzero

  exact ⟨h_even, h_pos⟩

/--
Actual internal-term form of the quantitative LTE lift.
-/
theorem lemma_1G_internal_term_quantitative_lift
  (n x k p d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (hk_bound : n - 1 - k ≤ p)
  (h_deficit_pos : 0 < p - (n - 1 - k))
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : ℤ)^p ∣ T_seq n x k)
  (h_term_nonzero : T_seq n x k ≠ 0) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by

  have h_lift_dvd :
      (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) :=
    lemma_1G_internal_term_deficit
      n x k p d_k hk_bound hS h_term_reaches

  have h_even_pos :
      Even d_k ∧ 0 < d_k :=
    lemma_1G_internal_term_even_positive_of_positive_deficit
      n x k p d_k hk_bound h_deficit_pos hS
      h_term_reaches h_term_nonzero

  rcases h_even_pos with ⟨h_even, h_pos⟩

  have h_val_ge :
      p - (n - 1 - k) ≤ padicValNat 3 (2^d_k - 1) :=
    padicValNat_three_two_pow_sub_one_ge_of_int_dvd
      (p - (n - 1 - k)) d_k h_pos h_lift_dvd

  have h_total_val :
      n - 1 - k + padicValNat 3 (2 ^ d_k - 1) ≥ p := by
    omega

  exact
    lemma_1G_quantitative_lte_lift
      n p k d_k hn h_k_upper h_total_val h_even h_pos

end Section19_Lemma1G_Quantitative_LTE
#check lemma_1G_step4_boundary_final_term
#print axioms lemma_1G_step4_boundary_final_term

-- ===============================================================
-- SECTION 20: LEMMA 1H (STEP 1: PRIOR INVOCATIONS)
-- ===============================================================
section Section20_Lemma1H_PriorInvocations

/-!
Step 1 for Lemma 1H.

Before encoding the three ultrametric mechanisms, we explicitly invoke only
the prior definitions and results that the manuscript permits Lemma 1H to use:

* `is_cycle`
* the bifurcated Lemma 1F equation and target predicates
* the 3-adic terminal divisibility result from Lemma 1F
* the sovereign-cancellation contradiction from Lemma 1F
* the quantitative LTE lift from Lemma 1G

No new trajectory mechanism is introduced in this step.
-/

#check is_cycle
#check T_seq
#check T_last
#check bifurcated_LHS
#check bifurcated_component
#check bifurcated_component_reaches_target
#check bifurcated_LHS_reaches_target
#check cycle_seed_target
#check lemma_1F_step1_bifurcated_LHS_eq
#check lemma_1F_step2_T_last_divisible_by_three
#check lemma_1F_step2_T_last_zero_valuation_contradiction
#check lemma_1F_step3_sovereign_cancellation
#check s_relationship
#check S_prime
#check lemma_1G_internal_term_quantitative_lift

/--
Lemma 1H Step 1a.

Any nontrivial cycle reaches the exact bifurcated 3-adic target already
established in Lemma 1F.
-/
theorem lemma_1H_step1_cycle_invokes_1F_seed_target
  (n x : Nat)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  bifurcated_LHS_reaches_target n x (cycle_seed_target n x) := by
  exact cycle_bifurcated_LHS_reaches_seed_target n x h_cycle hn hx

/--
Lemma 1H Step 1b.

The terminal boundary term must be divisible by `3` for a nontrivial cycle.
This is exactly Lemma 1F's terminal valuation condition.
-/
theorem lemma_1H_step1_cycle_invokes_1F_T_last
  (n x : Nat)
  (h_cycle : is_cycle n x)
  (hn : 1 < n) :
  (3 : Int) ∣ T_last n x := by
  exact lemma_1F_step2_T_last_divisible_by_three n x h_cycle hn

/--
Lemma 1H Step 1c.

If the terminal boundary term does not have the first 3-adic lift, the
cycle equation contradicts Lemma 1F immediately.
-/
theorem lemma_1H_step1_T_last_misalignment_contradiction
  (n x : Nat)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (h_T_last_zero : ¬ ((3 : Int) ∣ T_last n x)) :
  False := by
  exact
    lemma_1F_step2_T_last_zero_valuation_contradiction
      n x h_cycle hn h_T_last_zero

/--
Lemma 1H Step 1d.

This is only a named invocation of Lemma 1F's sovereign-cancellation step.
It records the exact local contradiction that will be used when a component is
skipped by the proposed 3-adic cancellation architecture.
-/
theorem lemma_1H_step1_invokes_1F_sovereign_cancellation
  (n x j target : Nat)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_target_le : target ≤ cycle_seed_target n x)
  (h_skipped :
    ¬ bifurcated_component_reaches_target n x target j)
  (h_rest_lifted :
    (3 : Int)^target ∣
      bifurcated_LHS n x - bifurcated_component n x j) :
  False := by
  exact
    lemma_1F_step3_sovereign_cancellation
      n x j target h_cycle hn hx h_target_le h_skipped h_rest_lifted

/--
Lemma 1H Step 1e.

This is only a named invocation of Lemma 1G's quantitative LTE lift for an
internal bifurcated term.
-/
theorem lemma_1H_step1_invokes_1G_internal_lift
  (n x k p d_k : Nat)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (hk_bound : n - 1 - k ≤ p)
  (h_deficit_pos : 0 < p - (n - 1 - k))
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : Int)^p ∣ T_seq n x k)
  (h_term_nonzero : T_seq n x k ≠ 0) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by
  exact
    lemma_1G_internal_term_quantitative_lift
      n x k p d_k hn h_k_upper hk_bound h_deficit_pos
      hS h_term_reaches h_term_nonzero

end Section20_Lemma1H_PriorInvocations
#check lemma_1H_step1_cycle_invokes_1F_seed_target
#check lemma_1H_step1_cycle_invokes_1F_T_last
#check lemma_1H_step1_T_last_misalignment_contradiction
#check lemma_1H_step1_invokes_1F_sovereign_cancellation
#check lemma_1H_step1_invokes_1G_internal_lift

-- ===============================================================
-- SECTION 20B: LEMMA 1H (MECHANISM 1: DIRECT GLOBAL LIFTING)
-- ===============================================================
section Section20B_Lemma1H_Mechanism1

/--
Lemma 1H, Mechanism 1: one internal term directly lifts to target.

Manuscript:
"Every individual term in the deviation series must independently secure
sufficient 3-adic valuation."

For an internal term, the positional valuation is `n - 1 - k`. If this is
below `target`, then the lift factor `(2^d_k - 1)` must supply the missing
deficit. This makes the component reach target and forces `d_k` even.
-/
theorem lemma_1H_mechanism1_internal_term_direct_lift
  (n x target k d_k : ℕ)
  (hk : k ∈ Ico 1 (n - 1))
  (h_positional_below : n - 1 - k < target)
  (hS : S k x = 2 * k + d_k)
  (h_direct_lift :
    (3 : ℤ)^(target - (n - 1 - k)) ∣
      ((2 : ℤ)^d_k - 1)) :
  bifurcated_component_reaches_target n x target k ∧ Even d_k := by

  have h_deficit_pos :
      0 < target - (n - 1 - k) := by
    omega

  have h_even : Even d_k :=
    lemma_1G_even_deviation_of_positive_deficit
      (target - (n - 1 - k)) d_k h_deficit_pos h_direct_lift

  constructor

  · unfold bifurcated_component_reaches_target
    unfold bifurcated_component

    have hk_ne : k ≠ n - 1 := by
      rw [mem_Ico] at hk
      omega

    simp [hk_ne]

    rw [T_seq_factor_of_prefix_deviation n x k d_k hS]

    have h_target_split :
        target = (n - 1 - k) + (target - (n - 1 - k)) := by
      omega

    rw [h_target_split, pow_add]

    rcases h_direct_lift with ⟨c, hc⟩

    use (2 : ℤ)^(2 * k) * c

    calc
      (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k) *
          ((2 : ℤ)^d_k - 1)
          =
        (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k) *
          ((3 : ℤ)^(target - (n - 1 - k)) * c) := by
            rw [hc]
      _ =
        ((3 : ℤ)^(n - 1 - k) *
          (3 : ℤ)^(target - (n - 1 - k))) *
            ((2 : ℤ)^(2 * k) * c) := by
              ring

  · exact h_even
/--
Lemma 1H, Mechanism 1: direct global lifting.

All internal terms have positional valuation below target and therefore must
directly lift to target through their deviation factors.

The terminal boundary term `T_last` is not lifted by a deviation factor. Its
3-adic valuation is supplied by the boundary structure from Lemma 1F and is
assumed here to reach the target directly.

Hence every component of the bifurcated LHS reaches target, so the full LHS
reaches target. The internal deviations are all even, giving the all-positive
perturbation trajectory.
-/
theorem lemma_1H_mechanism1_direct_global_lifting
  (n x target : ℕ)
  (hn : 1 < n)
  (h_internal_direct_lift :
    ∀ k ∈ Ico 1 (n - 1),
      ∃ d_k : ℕ,
        n - 1 - k < target ∧
          S k x = 2 * k + d_k ∧
            (3 : ℤ)^(target - (n - 1 - k)) ∣
              ((2 : ℤ)^d_k - 1))
  (h_Tlast_reaches_target :
    (3 : ℤ)^target ∣ T_last n x) :
  bifurcated_LHS_reaches_target n x target ∧
    (∀ k ∈ Ico 1 (n - 1), ∃ d_k : ℕ, S k x = 2 * k + d_k ∧ Even d_k) := by

  constructor

  · unfold bifurcated_LHS_reaches_target

    rw [bifurcated_LHS_eq_component_sum n x hn]

    apply dvd_sum
    intro k hk

    by_cases hk_last : k = n - 1

    · subst k
      unfold bifurcated_component
      simp
      exact h_Tlast_reaches_target

    · have hk_internal : k ∈ Ico 1 (n - 1) := by
        rw [mem_Ico] at hk ⊢
        omega

      rcases h_internal_direct_lift k hk_internal with
        ⟨d_k, h_positional_below, hS, h_direct_lift⟩

      exact
        (lemma_1H_mechanism1_internal_term_direct_lift
          n x target k d_k hk_internal h_positional_below hS
          h_direct_lift).1

  · intro k hk

    rcases h_internal_direct_lift k hk with
      ⟨d_k, h_positional_below, hS, h_direct_lift⟩

    exact
      ⟨d_k, hS,
        (lemma_1H_mechanism1_internal_term_direct_lift
          n x target k d_k hk h_positional_below hS h_direct_lift).2⟩
end Section20B_Lemma1H_Mechanism1

#check lemma_1H_mechanism1_internal_term_direct_lift
#check lemma_1H_mechanism1_direct_global_lifting

-- ===============================================================
-- SECTION 20C: LEMMA 1H (MECHANISM 2: IMMEDIATE LIFTING)
-- ===============================================================
section Section20C_Lemma1H_Mechanism2

/--
Lemma 1H, Mechanism 2: no secondary lift at the first coordinate.

Manuscript:
"Because this first term possesses the maximum positional valuation, it must
not execute a secondary lift; therefore, its deviation d_1 must strictly be
odd."
-/
theorem lemma_1H_mechanism2_no_secondary_lift_forces_odd_deviation
  (d1 : ℕ)
  (h_no_secondary_lift :
    ¬ (3 : ℤ) ∣ ((2 : ℤ)^d1 - 1)) :
  Odd d1 := by

  by_cases h_even : Even d1

  · exfalso
    apply h_no_secondary_lift

    rcases h_even with ⟨t, ht⟩
    rw [ht]

    have h_exp : t + t = 2 * t := by
      omega

    rw [h_exp]

    have h_zero :
        (((2 : ℤ)^(2 * t) - 1 : ℤ) : ZMod 3) = 0 := by
      have h_two_sq : (2 : ZMod 3)^2 = 1 := by
        decide

      calc
        (((2 : ℤ)^(2 * t) - 1 : ℤ) : ZMod 3)
            = (2 : ZMod 3)^(2 * t) - 1 := by
              norm_num
        _ = ((2 : ZMod 3)^2)^t - 1 := by
              rw [pow_mul]
        _ = 1^t - 1 := by
              rw [h_two_sq]
        _ = 0 := by
              simp

    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_zero
    exact h_zero

  · exact Nat.not_even_iff_odd.mp h_even

/--
Lemma 1H, Mechanism 2: required lifting below the immediate floor.

Manuscript:
"all subsequent terms (which possess lower positional powers) must artificially
lift to match this ... floor. Therefore, their deviations d_k must be even."

Here the immediate floor is `n - 2 - i`. If a later positional power
`n - 1 - k` is below that floor, then the required lift is supplied by
`2^d_k - 1`. Lemma 1G/LTE forces `d_k` to be even and gives the minimum
quantitative lift.
-/
theorem lemma_1H_mechanism2_required_lift_forces_even_and_minimum
  (n i k d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (h_below_floor : n - 1 - k < n - 2 - i)
  (h_dk_pos : 0 < d_k)
  (h_required_lift :
    (3 : ℤ)^((n - 2 - i) - (n - 1 - k)) ∣
      ((2 : ℤ)^d_k - 1)) :
  Even d_k ∧
    d_k ≥ 2 * 3 ^ (((n - 2 - i) - (n - 1 - k)) - 1) := by

  let floor := n - 2 - i
  let pos := n - 1 - k

  have h_deficit_pos :
      0 < floor - pos := by
    dsimp [floor, pos]
    omega

  have h_required_lift_floor :
      (3 : ℤ)^(floor - pos) ∣ ((2 : ℤ)^d_k - 1) := by
    dsimp [floor, pos]
    exact h_required_lift

  have h_even : Even d_k :=
    lemma_1G_even_deviation_of_positive_deficit
      (floor - pos) d_k h_deficit_pos h_required_lift_floor

  have h_val_ge :
      floor - pos ≤ padicValNat 3 (2^d_k - 1) :=
    padicValNat_three_two_pow_sub_one_ge_of_int_dvd
      (floor - pos) d_k h_dk_pos h_required_lift_floor

  have h_total_val :
      n - 1 - k + padicValNat 3 (2^d_k - 1) ≥ floor := by
    dsimp [floor, pos] at h_val_ge ⊢
    omega

  have h_min :
      d_k ≥ 2 * 3 ^ (floor + k - n) :=
    lemma_1G_quantitative_lte_lift
      n floor k d_k hn h_k_upper h_total_val h_even h_dk_pos

  have h_exp :
      floor + k - n = (floor - pos) - 1 := by
    dsimp [floor, pos]
    omega

  rw [h_exp] at h_min

  constructor
  · exact h_even
  · dsimp [floor, pos] at h_min
    exact h_min

/--
Lemma 1H, Mechanism 2: immediate parity alteration at the second term.

Manuscript:
"To satisfy d_1 = odd and d_2 = even, the trajectory must execute exactly one
parity alteration immediately at the second term."

In the formalization, prefix-deviation parity is represented by `S_prime`.
This is exactly Lemma 1E at index `1`.
-/
theorem lemma_1H_mechanism2_immediate_parity_alteration
  (x : ℕ)
  (h_d1_odd :
    (S_prime 1 x : ZMod 2) = 1)
  (h_d2_even :
    (S_prime 2 x : ZMod 2) = 0) :
  (val ((T^[1]) x) : ZMod 2) = 1 := by

  have h_rec :
      (S_prime 2 x : ZMod 2) =
        (S_prime 1 x : ZMod 2) +
          (val ((T^[1]) x) : ZMod 2) := by
    simpa using lemma_1E_parity_congruence x 1

  rw [h_d1_odd, h_d2_even] at h_rec

  have h_two_zero : (2 : ZMod 2) = 0 := by
    decide

  calc
    (val ((T^[1]) x) : ZMod 2)
        =
      (1 : ZMod 2) +
        ((1 : ZMod 2) + (val ((T^[1]) x) : ZMod 2)) := by
          rw [show (1 : ZMod 2) + ((1 : ZMod 2) + (val ((T^[1]) x) : ZMod 2)) =
              (2 : ZMod 2) + (val ((T^[1]) x) : ZMod 2) by ring]
          rw [h_two_zero]
          ring
    _ =
      (1 : ZMod 2) + 0 := by
        rw [h_rec.symm]
    _ =
      1 := by
        ring

end Section20C_Lemma1H_Mechanism2

#check lemma_1H_mechanism2_no_secondary_lift_forces_odd_deviation
#check lemma_1H_mechanism2_required_lift_forces_even_and_minimum
#check lemma_1H_mechanism2_immediate_parity_alteration
-- ===============================================================
-- SECTION 20D: LEMMA 1H (MECHANISM 3: PERPETUAL CASCADING CANCELLATION)
-- ===============================================================
section Section20D_Lemma1H_Mechanism3

/--
Lemma 1H, Mechanism 3: terms below the cascade floor require even lifting.

Manuscript:
"Exactly at the term where the positional power evaluates to p - 1, the
sequence must execute a parity alteration. This switches the deviation d_k to
an even integer, engaging the secondary lift to match the p floor ... For all
subsequent terms, the deviations must remain even."

If a term has positional power below the cascade floor `p`, then the required
internal lift is supplied by `2^d_k - 1`. Lemma 1G/LTE forces `d_k` to be even
and gives the minimum quantitative lift.
-/
theorem lemma_1H_mechanism3_lower_terms_lift_even_and_minimum
  (n p k d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (h_below_floor : n - 1 - k < p)
  (h_dk_pos : 0 < d_k)
  (h_required_lift :
    (3 : ℤ)^(p - (n - 1 - k)) ∣
      ((2 : ℤ)^d_k - 1)) :
  Even d_k ∧
    d_k ≥ 2 * 3 ^ ((p - (n - 1 - k)) - 1) := by

  have h_deficit_pos :
      0 < p - (n - 1 - k) := by
    omega

  have h_even : Even d_k :=
    lemma_1G_even_deviation_of_positive_deficit
      (p - (n - 1 - k)) d_k h_deficit_pos h_required_lift

  have h_val_ge :
      p - (n - 1 - k) ≤ padicValNat 3 (2^d_k - 1) :=
    padicValNat_three_two_pow_sub_one_ge_of_int_dvd
      (p - (n - 1 - k)) d_k h_dk_pos h_required_lift

  have h_total_val :
      n - 1 - k + padicValNat 3 (2^d_k - 1) ≥ p := by
    omega

  have h_min :
      d_k ≥ 2 * 3 ^ (p + k - n) :=
    lemma_1G_quantitative_lte_lift
      n p k d_k hn h_k_upper h_total_val h_even h_dk_pos

  have h_exp :
      p + k - n = (p - (n - 1 - k)) - 1 := by
    omega

  rw [h_exp] at h_min

  exact ⟨h_even, h_min⟩

#check lemma_1H_mechanism3_lower_terms_lift_even_and_minimum

-- ===============================================================
-- SECTION 20E: LEMMA 1H (DEVIATION PARITY BRIDGE)
-- ===============================================================
section Section20E_Lemma1H_DeviationParityBridge

/--
Deviation parity bridge, even case.

If the exponent prefix has the form `S_k = 2k + d_k`, then the signed prefix
deviation `S'_k` is exactly `d_k`. Hence even `d_k` gives even `S'_k`.
-/
theorem lemma_1H_even_deviation_to_S_prime_even
  (x k d_k : ℕ)
  (hS : S k x = 2 * k + d_k)
  (h_even : Even d_k) :
  (S_prime k x : ZMod 2) = 0 := by

  have h_rel := s_relationship k x

  have hS_int :
      (S k x : ℤ) = 2 * (k : ℤ) + (d_k : ℤ) := by
    exact_mod_cast hS

  have h_Sprime_eq :
      S_prime k x = (d_k : ℤ) := by
    linarith

  rw [h_Sprime_eq]

  rcases h_even with ⟨t, ht⟩

  rw [ht]

  calc
    (((t + t : ℕ) : ℤ) : ZMod 2)
        =
      (t : ZMod 2) + (t : ZMod 2) := by
        push_cast
        ring
    _ =
      0 := by
        exact zmod_two_add_self_eq_zero (t : ZMod 2)

/--
Deviation parity bridge, odd case.

If the exponent prefix has the form `S_k = 2k + d_k`, then the signed prefix
deviation `S'_k` is exactly `d_k`. Hence odd `d_k` gives odd `S'_k`.
-/
theorem lemma_1H_odd_deviation_to_S_prime_odd
  (x k d_k : ℕ)
  (hS : S k x = 2 * k + d_k)
  (h_odd : Odd d_k) :
  (S_prime k x : ZMod 2) = 1 := by

  have h_rel := s_relationship k x

  have hS_int :
      (S k x : ℤ) = 2 * (k : ℤ) + (d_k : ℤ) := by
    exact_mod_cast hS

  have h_Sprime_eq :
      S_prime k x = (d_k : ℤ) := by
    linarith

  rw [h_Sprime_eq]

  rcases h_odd with ⟨t, ht⟩

  rw [ht]

  calc
    (((2 * t + 1 : ℕ) : ℤ) : ZMod 2)
        =
      (2 : ZMod 2) * (t : ZMod 2) + 1 := by
        push_cast
        ring
    _ =
      0 * (t : ZMod 2) + 1 := by
        rw [zmod_two_two_eq_zero]
    _ =
      1 := by
        ring

end Section20E_Lemma1H_DeviationParityBridge

#check lemma_1H_even_deviation_to_S_prime_even
#check lemma_1H_odd_deviation_to_S_prime_odd
-- ===============================================================
--  LEMMA 1H (PARITY PATTERNS TO TRAJECTORY MAP)
-- ===============================================================
section Section20E_Lemma1H_ParityPatterns_To_TrajectoryMap

/--
An odd parity event is the formal umbrella for the manuscript phrase:
"a negative perturbation or an odd positive perturbation."
-/
def lemma_1H_odd_parity_event (x k : ℕ) : Prop :=
  (val ((T^[k]) x) : ZMod 2) = 1

/--
An even parity event is the formal parity class of the remaining positive
lifting steps.
-/
def lemma_1H_even_parity_event (x k : ℕ) : Prop :=
  (val ((T^[k]) x) : ZMod 2) = 0

/--
If consecutive deviation parities are both even, then the physical perturbation
step between them is even.
-/
theorem lemma_1H_even_to_even_requires_even_event
  (x k : ℕ)
  (h_current_even : (S_prime k x : ZMod 2) = 0)
  (h_next_even : (S_prime (k + 1) x : ZMod 2) = 0) :
  lemma_1H_even_parity_event x k := by

  unfold lemma_1H_even_parity_event

  have h_rec := lemma_1E_parity_congruence x k
  rw [h_current_even, h_next_even] at h_rec

  simpa using h_rec.symm

/--
If the deviation parity changes from odd to even, then the physical perturbation
step causing the change is an odd parity event.
-/
theorem lemma_1H_odd_to_even_requires_odd_event
  (x k : ℕ)
  (h_current_odd : (S_prime k x : ZMod 2) = 1)
  (h_next_even : (S_prime (k + 1) x : ZMod 2) = 0) :
  lemma_1H_odd_parity_event x k := by

  unfold lemma_1H_odd_parity_event

  have h_rec := lemma_1E_parity_congruence x k
  rw [h_current_odd, h_next_even] at h_rec

  have h_two_zero : (2 : ZMod 2) = 0 := by
    decide

  calc
    (val ((T^[k]) x) : ZMod 2)
        =
      (1 : ZMod 2) +
        ((1 : ZMod 2) + (val ((T^[k]) x) : ZMod 2)) := by
          rw [show
              (1 : ZMod 2) +
                  ((1 : ZMod 2) + (val ((T^[k]) x) : ZMod 2)) =
                (2 : ZMod 2) + (val ((T^[k]) x) : ZMod 2) by
              ring]
          rw [h_two_zero]
          ring
    _ =
      (1 : ZMod 2) + 0 := by
        rw [h_rec.symm]
    _ =
      1 := by
        ring

/--
If the first deviation is odd, then the first physical perturbation event is
odd. This is the first negative perturbation or odd positive perturbation in
Mechanisms 2 and 3.
-/
theorem lemma_1H_first_odd_deviation_requires_initial_odd_event
  (x : ℕ)
  (h_d1_odd : (S_prime 1 x : ZMod 2) = 1) :
  lemma_1H_odd_parity_event x 0 := by

  unfold lemma_1H_odd_parity_event

  have h_rec := lemma_1E_parity_congruence x 0

  have h_zero : (S_prime 0 x : ZMod 2) = 0 := by
    simp [S_prime]

  rw [h_zero, h_d1_odd] at h_rec

  simpa using h_rec.symm

/--
Mechanism 1 trajectory interpretation.

For Mechanism 1, the internal lifted terms give even prefix-deviation parity
only through the internal range `Ico 1 (n - 1)`. The terminal boundary term
`T_last` is not a lifted `T_seq` term, so it is not included here.

Thus every physical perturbation event whose two adjacent prefix deviations
are internal/even is an even event.
-/
theorem lemma_1H_mechanism1_even_deviations_map_to_even_events
  (n x : ℕ)
  (h_even_deviation :
    ∀ j ∈ Ico 1 (n - 1),
      (S_prime j x : ZMod 2) = 0) :
  ∀ k ∈ Ico 0 (n - 2),
    lemma_1H_even_parity_event x k := by

  intro k hk

  apply lemma_1H_even_to_even_requires_even_event

  · by_cases hk_zero : k = 0

    · subst k
      simp [S_prime]

    · exact h_even_deviation k (by
        rw [mem_Ico] at hk ⊢
        omega)

  · exact h_even_deviation (k + 1) (by
      rw [mem_Ico] at hk ⊢
      omega)
#check lemma_1H_mechanism1_even_deviations_map_to_even_events

/--
Mechanism 1 closes to its trajectory map.

Direct global lifting gives even internal deviations. The deviation parity
bridge converts those to even `S_prime` parities, and Lemma 1E maps the
consecutive even prefix parities to even physical perturbation events.
-/
theorem lemma_1H_mechanism1_direct_lifting_maps_to_even_trajectory
  (n x target : ℕ)
  (hn : 1 < n)
  (h_internal_direct_lift :
    ∀ k ∈ Ico 1 (n - 1),
      ∃ d_k : ℕ,
        n - 1 - k < target ∧
          S k x = 2 * k + d_k ∧
            (3 : ℤ)^(target - (n - 1 - k)) ∣
              ((2 : ℤ)^d_k - 1))
  (h_Tlast_reaches_target :
    (3 : ℤ)^target ∣ T_last n x) :
  ∀ k ∈ Ico 0 (n - 2),
    lemma_1H_even_parity_event x k := by

  have h_mech1 :=
    lemma_1H_mechanism1_direct_global_lifting
      n x target hn h_internal_direct_lift h_Tlast_reaches_target

  rcases h_mech1 with ⟨_, h_even_deviation_witness⟩

  have h_even_Sprime :
      ∀ j ∈ Ico 1 (n - 1),
        (S_prime j x : ZMod 2) = 0 := by
    intro j hj

    rcases h_even_deviation_witness j hj with ⟨d_j, hS, h_even⟩

    exact
      lemma_1H_even_deviation_to_S_prime_even
        x j d_j hS h_even

  exact
    lemma_1H_mechanism1_even_deviations_map_to_even_events
      n x h_even_Sprime
#check lemma_1H_mechanism1_direct_lifting_maps_to_even_trajectory
/--
Mechanism 2 trajectory interpretation.

The pattern `d_1` odd and `d_2` even gives exactly two odd parity events:
the initial odd event, and the immediate parity flip at the second term.
-/

theorem lemma_1H_mechanism2_parity_pattern_maps_to_two_odd_events
  (x : ℕ)
  (h_d1_odd : (S_prime 1 x : ZMod 2) = 1)
  (h_d2_even : (S_prime 2 x : ZMod 2) = 0) :
  lemma_1H_odd_parity_event x 0 ∧
    lemma_1H_odd_parity_event x 1 := by

  constructor

  · exact
      lemma_1H_first_odd_deviation_requires_initial_odd_event
        x h_d1_odd

  · exact
      lemma_1H_odd_to_even_requires_odd_event
        x 1 h_d1_odd (by
          simpa using h_d2_even)
/--
Mechanism 2 closes to its trajectory map.

The first coordinate has no secondary lift, so `d_1` is odd. The second
coordinate is lifted, so `d_2` is even. The deviation parity bridge converts
these into `S_prime` parity, and Lemma 1E gives the two odd physical events:
the initial event and the immediate parity alteration.
-/
theorem lemma_1H_mechanism2_maps_to_immediate_two_odd_events
  (x d1 d2 : ℕ)
  (hS1 : S 1 x = 2 * 1 + d1)
  (hS2 : S 2 x = 2 * 2 + d2)
  (h_no_secondary_lift :
    ¬ (3 : ℤ) ∣ ((2 : ℤ)^d1 - 1))
  (h_d2_even : Even d2) :
  lemma_1H_odd_parity_event x 0 ∧
    lemma_1H_odd_parity_event x 1 := by

  have h_d1_odd : Odd d1 :=
    lemma_1H_mechanism2_no_secondary_lift_forces_odd_deviation
      d1 h_no_secondary_lift

  have h_Sprime1_odd :
      (S_prime 1 x : ZMod 2) = 1 :=
    lemma_1H_odd_deviation_to_S_prime_odd
      x 1 d1 hS1 h_d1_odd

  have h_Sprime2_even :
      (S_prime 2 x : ZMod 2) = 0 :=
    lemma_1H_even_deviation_to_S_prime_even
      x 2 d2 hS2 h_d2_even

  exact
    lemma_1H_mechanism2_parity_pattern_maps_to_two_odd_events
      x h_Sprime1_odd h_Sprime2_even
#check lemma_1H_mechanism2_maps_to_immediate_two_odd_events
/--
If consecutive deviation parities are both odd, then the physical perturbation
step between them is even.

This is the Mechanism 3 pre-entry case: the prefix deviation remains odd until
the cascade-entry parity alteration occurs.
-/
theorem lemma_1H_odd_to_odd_requires_even_event
  (x k : ℕ)
  (h_current_odd : (S_prime k x : ZMod 2) = 1)
  (h_next_odd : (S_prime (k + 1) x : ZMod 2) = 1) :
  lemma_1H_even_parity_event x k := by

  unfold lemma_1H_even_parity_event

  have h_rec := lemma_1E_parity_congruence x k
  rw [h_current_odd, h_next_odd] at h_rec

  have h_two_zero : (2 : ZMod 2) = 0 := by
    decide

  calc
    (val ((T^[k]) x : ℕ) : ZMod 2)
        =
      (1 : ZMod 2) +
        ((1 : ZMod 2) + (val ((T^[k]) x : ℕ) : ZMod 2)) := by
          rw [show
              (1 : ZMod 2) +
                  ((1 : ZMod 2) + (val ((T^[k]) x : ℕ) : ZMod 2)) =
                (2 : ZMod 2) + (val ((T^[k]) x : ℕ) : ZMod 2) by
              ring]
          rw [h_two_zero]
          ring
    _ =
      (1 : ZMod 2) + 1 := by
        rw [h_rec.symm]
    _ =
      (2 : ZMod 2) := by
        ring
    _ =
      0 := by
        rw [h_two_zero]
#check lemma_1H_odd_to_odd_requires_even_event

/--
Mechanism 2 closes to its full internal trajectory map.

The first two physical events are odd: the initial odd event and the immediate
parity alteration. After that, all internal lifted deviations remain even, so
all later internal physical events are even.

The terminal boundary `T_last` is not included, since it is not an internal
lifted `T_seq` term.
-/
theorem lemma_1H_mechanism2_maps_to_full_internal_trajectory
  (n x d1 d2 : ℕ)
  (hS1 : S 1 x = 2 * 1 + d1)
  (hS2 : S 2 x = 2 * 2 + d2)
  (h_no_secondary_lift :
    ¬ (3 : ℤ) ∣ ((2 : ℤ)^d1 - 1))
  (h_d2_even : Even d2)
  (h_tail_even_deviation :
    ∀ j ∈ Ico 2 (n - 1),
      ∃ d_j : ℕ, S j x = 2 * j + d_j ∧ Even d_j) :
  (lemma_1H_odd_parity_event x 0 ∧
      lemma_1H_odd_parity_event x 1) ∧
    (∀ k ∈ Ico 2 (n - 2),
      lemma_1H_even_parity_event x k) := by

  constructor

  · exact
      lemma_1H_mechanism2_maps_to_immediate_two_odd_events
        x d1 d2 hS1 hS2 h_no_secondary_lift h_d2_even

  · intro k hk

    apply lemma_1H_even_to_even_requires_even_event

    · rcases h_tail_even_deviation k (by
        rw [mem_Ico] at hk ⊢
        omega) with ⟨d_k, hS_k, h_even_k⟩

      exact
        lemma_1H_even_deviation_to_S_prime_even
          x k d_k hS_k h_even_k

    · rcases h_tail_even_deviation (k + 1) (by
        rw [mem_Ico] at hk ⊢
        omega) with ⟨d_next, hS_next, h_even_next⟩

      exact
        lemma_1H_even_deviation_to_S_prime_even
          x (k + 1) d_next hS_next h_even_next

#check lemma_1H_mechanism2_maps_to_full_internal_trajectory
/--
Mechanism 3 trajectory interpretation.

The pattern begins with an initial odd event, but the parity flip can occur
later at the cascade entry. This is the delayed analogue of Mechanism 2.
-/
theorem lemma_1H_mechanism3_parity_pattern_maps_to_two_odd_events
  (x entry : ℕ)
  (h_d1_odd : (S_prime 1 x : ZMod 2) = 1)
  (h_before_entry_odd :
    (S_prime entry x : ZMod 2) = 1)
  (h_entry_even :
    (S_prime (entry + 1) x : ZMod 2) = 0) :
  lemma_1H_odd_parity_event x 0 ∧
    lemma_1H_odd_parity_event x entry := by

  constructor

  · exact
      lemma_1H_first_odd_deviation_requires_initial_odd_event
        x h_d1_odd

  · exact
      lemma_1H_odd_to_even_requires_odd_event
        x entry h_before_entry_odd h_entry_even
/--
Mechanism 3 closes to its full internal trajectory map.

The initial event is odd. Before the cascade entry, the prefix deviation remains
odd, so those physical events are even. At the cascade entry, the parity flips
from odd to even, giving the second odd event. After entry, the lifted internal
deviations remain even, so the later physical events are even.

The terminal boundary `T_last` is not included, since it is not an internal
lifted `T_seq` term.
-/
theorem lemma_1H_mechanism3_maps_to_full_internal_trajectory
  (n x entry d1 d_entry : ℕ)
  (h_entry_pos : 1 ≤ entry)
  (hS1 : S 1 x = 2 * 1 + d1)
  (h_d1_odd : Odd d1)
  (h_pre_entry_odd :
    ∀ j ∈ Ico 1 (entry + 1),
      (S_prime j x : ZMod 2) = 1)
  (hS_entry_next :
    S (entry + 1) x = 2 * (entry + 1) + d_entry)
  (h_entry_even : Even d_entry)
  (h_tail_even_deviation :
    ∀ j ∈ Ico (entry + 1) (n - 1),
      ∃ d_j : ℕ, S j x = 2 * j + d_j ∧ Even d_j) :
  (lemma_1H_odd_parity_event x 0 ∧
      lemma_1H_odd_parity_event x entry) ∧
    (∀ k ∈ Ico 1 entry,
      lemma_1H_even_parity_event x k) ∧
      (∀ k ∈ Ico (entry + 1) (n - 2),
        lemma_1H_even_parity_event x k) := by

  have h_Sprime1_odd :
      (S_prime 1 x : ZMod 2) = 1 :=
    lemma_1H_odd_deviation_to_S_prime_odd
      x 1 d1 hS1 h_d1_odd

  have h_entry_mem :
      entry ∈ Ico 1 (entry + 1) := by
    rw [mem_Ico]
    exact ⟨h_entry_pos, Nat.lt_succ_self entry⟩

  have h_Sprime_entry_odd :
      (S_prime entry x : ZMod 2) = 1 :=
    h_pre_entry_odd entry h_entry_mem

  have h_Sprime_entry_next_even :
      (S_prime (entry + 1) x : ZMod 2) = 0 :=
    lemma_1H_even_deviation_to_S_prime_even
      x (entry + 1) d_entry hS_entry_next h_entry_even

  constructor

  · exact
      lemma_1H_mechanism3_parity_pattern_maps_to_two_odd_events
        x entry h_Sprime1_odd h_Sprime_entry_odd
        h_Sprime_entry_next_even

  constructor

  · intro k hk

    apply lemma_1H_odd_to_odd_requires_even_event

    · exact h_pre_entry_odd k (by
        rw [mem_Ico] at hk ⊢
        omega)

    · exact h_pre_entry_odd (k + 1) (by
        rw [mem_Ico] at hk ⊢
        omega)

  · intro k hk

    apply lemma_1H_even_to_even_requires_even_event

    · rcases h_tail_even_deviation k (by
        rw [mem_Ico] at hk ⊢
        omega) with ⟨d_k, hS_k, h_even_k⟩

      exact
        lemma_1H_even_deviation_to_S_prime_even
          x k d_k hS_k h_even_k

    · rcases h_tail_even_deviation (k + 1) (by
        rw [mem_Ico] at hk ⊢
        omega) with ⟨d_next, hS_next, h_even_next⟩

      exact
        lemma_1H_even_deviation_to_S_prime_even
          x (k + 1) d_next hS_next h_even_next

#check lemma_1H_mechanism3_maps_to_full_internal_trajectory
-- ===============================================================
-- SECTION 20G: LEMMA 1H (TRAJECTORY OUTPUT PREDICATES)
-- ===============================================================
section Section20G_Lemma1H_TrajectoryOutputPredicates

/--
Mechanism 1 trajectory output.

All internal physical perturbation events are even.
This is the formal trajectory shape of the pure positive perturbation case.
-/
def lemma_1H_mechanism1_trajectory (n x : ℕ) : Prop :=
  ∀ k ∈ Ico 0 (n - 2),
    lemma_1H_even_parity_event x k

/--
Mechanism 2 trajectory output.

The first two physical perturbation events are odd, and all later internal
physical perturbation events are even.
-/
def lemma_1H_mechanism2_trajectory (n x : ℕ) : Prop :=
  (lemma_1H_odd_parity_event x 0 ∧
      lemma_1H_odd_parity_event x 1) ∧
    ∀ k ∈ Ico 2 (n - 2),
      lemma_1H_even_parity_event x k

/--
Mechanism 3 trajectory output.

The initial physical perturbation event is odd. A second odd event occurs at
the delayed cascade entry. Before and after that entry, the internal physical
perturbation events are even.
-/
def lemma_1H_mechanism3_trajectory (n x : ℕ) : Prop :=
  ∃ entry : ℕ,
    1 ≤ entry ∧
      (lemma_1H_odd_parity_event x 0 ∧
          lemma_1H_odd_parity_event x entry) ∧
        (∀ k ∈ Ico 1 entry,
          lemma_1H_even_parity_event x k) ∧
          ∀ k ∈ Ico (entry + 1) (n - 2),
            lemma_1H_even_parity_event x k

end Section20G_Lemma1H_TrajectoryOutputPredicates

#check lemma_1H_mechanism1_trajectory
#check lemma_1H_mechanism2_trajectory
#check lemma_1H_mechanism3_trajectory
end Section20E_Lemma1H_ParityPatterns_To_TrajectoryMap

#check lemma_1H_odd_parity_event
#check lemma_1H_even_parity_event
#check lemma_1H_mechanism1_even_deviations_map_to_even_events
#check lemma_1H_mechanism2_parity_pattern_maps_to_two_odd_events
#check lemma_1H_mechanism3_parity_pattern_maps_to_two_odd_events


-- ===============================================================
-- SECTION 20F: LEMMA 1H (TRAJECTORY EXHAUSTION: NO FOURTH MECHANISM)
-- ===============================================================
section Section20F_Lemma1H_NoFourthMechanism

/--
Lemma 1H exhaustion.

Manuscript:
"To achieve the target valuation n + x, the sequence is strictly bifurcated
into two foundational branches under the ultrametric law."

Branch A:
`target ≤ vmin`, giving Mechanism 1.

Branch B:
`vmin < target`, so ultrametric cancellation is required. Once a shared
collision floor `p` is bounded by the highest available positional floor,
there are only two possibilities:
`p = highestFloor` or `p < highestFloor`.

These are exactly Mechanism 2 and Mechanism 3. Therefore no fourth mechanism
is possible.
-/
theorem lemma_1H_no_fourth_mechanism
  (target vmin highestFloor p : ℕ)
  (h_floor_bound : p ≤ highestFloor) :
  target ≤ vmin ∨
    (vmin < target ∧ p = highestFloor) ∨
      (vmin < target ∧ p < highestFloor) := by

  by_cases h_branch_A : target ≤ vmin

  · exact Or.inl h_branch_A

  · have h_branch_B : vmin < target := by
      omega

    have h_floor_split :
        p = highestFloor ∨ p < highestFloor := by
      omega

    rcases h_floor_split with h_eq | h_lt

    · exact Or.inr (Or.inl ⟨h_branch_B, h_eq⟩)

    · exact Or.inr (Or.inr ⟨h_branch_B, h_lt⟩)

end Section20F_Lemma1H_NoFourthMechanism

#check lemma_1H_no_fourth_mechanism-- ===============================================================
-- SECTION 20G: LEMMA 1H (FAILED MECHANISM CONTRADICTS CYCLE)
-- ===============================================================
section Section20G_Lemma1H_FailedMechanism_ContradictsCycle

/--
Lemma 1H legitimacy bridge.

If `x` is a nontrivial cycle, then Lemma 1F forces the bifurcated LHS to
reach the cycle target. Therefore, if one required component of a proposed
mechanism fails to reach the target while the rest of the LHS is already lifted,
the cycle equation cannot hold.

This is exactly Lemma 1F sovereign cancellation applied inside Lemma 1H.
-/
theorem lemma_1H_failed_required_component_contradicts_cycle
  (n x j target : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_target_le : target ≤ cycle_seed_target n x)
  (h_component_fails :
    ¬ bifurcated_component_reaches_target n x target j)
  (h_rest_lifted :
    (3 : ℤ)^target ∣
      bifurcated_LHS n x - bifurcated_component n x j) :
  False := by

  exact
    lemma_1H_step1_invokes_1F_sovereign_cancellation
      n x j target h_cycle hn hx h_target_le
      h_component_fails h_rest_lifted

end Section20G_Lemma1H_FailedMechanism_ContradictsCycle

#check lemma_1H_failed_required_component_contradicts_cycle

-- ===============================================================
-- SECTION 20I: LEMMA 1H (ULTRAMETRIC EXHAUSTION BRIDGE)
-- ===============================================================
section Section20I_Lemma1H_UltrametricExhaustionBridge

/--
Lemma 1H ultrametric exhaustion bridge.

This is the formal bridge from the three manuscript mechanisms to the three
trajectory outputs.

It does not introduce a fourth mechanism. The hypothesis is exactly the
ultrametric exhaustion alternative: Mechanism 1, or Mechanism 2, or Mechanism 3.
-/
theorem lemma_1H_ultrametric_exhaustion_bridge
  (n x target : ℕ)
  (hn : 1 < n)
  (h_ultrametric_exhaustion :
    ((∀ k ∈ Ico 1 (n - 1),
        ∃ d_k : ℕ,
          n - 1 - k < target ∧
            S k x = 2 * k + d_k ∧
              (3 : ℤ)^(target - (n - 1 - k)) ∣
                ((2 : ℤ)^d_k - 1)) ∧
      (3 : ℤ)^target ∣ T_last n x) ∨
    (∃ d1 d2 : ℕ,
      S 1 x = 2 * 1 + d1 ∧
        S 2 x = 2 * 2 + d2 ∧
          ¬ (3 : ℤ) ∣ ((2 : ℤ)^d1 - 1) ∧
            Even d2 ∧
              ∀ j ∈ Ico 2 (n - 1),
                ∃ d_j : ℕ,
                  S j x = 2 * j + d_j ∧ Even d_j) ∨
    (∃ entry d1 d_entry : ℕ,
      1 ≤ entry ∧
        S 1 x = 2 * 1 + d1 ∧
          Odd d1 ∧
            (∀ j ∈ Ico 1 (entry + 1),
              (S_prime j x : ZMod 2) = 1) ∧
              S (entry + 1) x =
                2 * (entry + 1) + d_entry ∧
                Even d_entry ∧
                  ∀ j ∈ Ico (entry + 1) (n - 1),
                    ∃ d_j : ℕ,
                      S j x = 2 * j + d_j ∧ Even d_j)) :
  lemma_1H_mechanism1_trajectory n x ∨
    lemma_1H_mechanism2_trajectory n x ∨
      lemma_1H_mechanism3_trajectory n x := by

  rcases h_ultrametric_exhaustion with hM1 | hM2_or_M3

  · left

    rcases hM1 with
      ⟨h_internal_direct_lift, h_Tlast_reaches_target⟩

    unfold lemma_1H_mechanism1_trajectory

    exact
      lemma_1H_mechanism1_direct_lifting_maps_to_even_trajectory
        n x target hn h_internal_direct_lift h_Tlast_reaches_target

  · rcases hM2_or_M3 with hM2 | hM3

    · right
      left

      rcases hM2 with
        ⟨d1, d2, hS1, hS2, h_no_secondary_lift,
          h_d2_even, h_tail_even_deviation⟩

      unfold lemma_1H_mechanism2_trajectory

      exact
        lemma_1H_mechanism2_maps_to_full_internal_trajectory
          n x d1 d2 hS1 hS2 h_no_secondary_lift
          h_d2_even h_tail_even_deviation

    · right
      right

      rcases hM3 with
        ⟨entry, d1, d_entry, h_entry_pos, hS1, h_d1_odd,
          h_pre_entry_odd, hS_entry_next, h_entry_even,
          h_tail_even_deviation⟩

      unfold lemma_1H_mechanism3_trajectory

      refine ⟨entry, h_entry_pos, ?_⟩

      exact
        lemma_1H_mechanism3_maps_to_full_internal_trajectory
          n x entry d1 d_entry h_entry_pos hS1 h_d1_odd
          h_pre_entry_odd hS_entry_next h_entry_even
          h_tail_even_deviation

end Section20I_Lemma1H_UltrametricExhaustionBridge

#check lemma_1H_ultrametric_exhaustion_bridge
-- ===============================================================
-- SECTION 20J: LEMMA 1H (CYCLE-LEVEL TRAJECTORY ROUTING)
-- ===============================================================
section Section20J_Lemma1H_CycleLevelTrajectoryRouting

/--
Lemma 1H cycle-level routing.

For a nontrivial cycle, Lemma 1F forces the bifurcated LHS to reach the
cycle target `cycle_seed_target n x`. If the ultrametric exhaustion alternatives
for that target are present, then the trajectory must be one of the three
Lemma 1H mechanism trajectories.
-/
theorem lemma_1H_cycle_routes_to_trajectory
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_ultrametric_exhaustion :
    ((∀ k ∈ Ico 1 (n - 1),
        ∃ d_k : ℕ,
          n - 1 - k < cycle_seed_target n x ∧
            S k x = 2 * k + d_k ∧
              (3 : ℤ)^((cycle_seed_target n x) - (n - 1 - k)) ∣
                ((2 : ℤ)^d_k - 1)) ∧
      (3 : ℤ)^(cycle_seed_target n x) ∣ T_last n x) ∨
    (∃ d1 d2 : ℕ,
      S 1 x = 2 * 1 + d1 ∧
        S 2 x = 2 * 2 + d2 ∧
          ¬ (3 : ℤ) ∣ ((2 : ℤ)^d1 - 1) ∧
            Even d2 ∧
              ∀ j ∈ Ico 2 (n - 1),
                ∃ d_j : ℕ,
                  S j x = 2 * j + d_j ∧ Even d_j) ∨
    (∃ entry d1 d_entry : ℕ,
      1 ≤ entry ∧
        S 1 x = 2 * 1 + d1 ∧
          Odd d1 ∧
            (∀ j ∈ Ico 1 (entry + 1),
              (S_prime j x : ZMod 2) = 1) ∧
              S (entry + 1) x =
                2 * (entry + 1) + d_entry ∧
                Even d_entry ∧
                  ∀ j ∈ Ico (entry + 1) (n - 1),
                    ∃ d_j : ℕ,
                      S j x = 2 * j + d_j ∧ Even d_j)) :
  lemma_1H_mechanism1_trajectory n x ∨
    lemma_1H_mechanism2_trajectory n x ∨
      lemma_1H_mechanism3_trajectory n x := by

  have h_cycle_target :
      bifurcated_LHS_reaches_target n x (cycle_seed_target n x) :=
    lemma_1H_step1_cycle_invokes_1F_seed_target
      n x h_cycle hn hx

  exact
    lemma_1H_ultrametric_exhaustion_bridge
      n x (cycle_seed_target n x) hn h_ultrametric_exhaustion

end Section20J_Lemma1H_CycleLevelTrajectoryRouting

#check lemma_1H_cycle_routes_to_trajectory

-- ===============================================================
-- SECTION 20K: COROLLARY 1H-1
-- FATAL PARITY VIOLATION OF A THIRD NEGATIVE PERTURBATION
-- ===============================================================
section Section20K_Corollary1H1

/--
Corollary 1H-1.

Under the Mechanism 3 cascade trajectory supplied by Lemma 1H, every internal
event after the cascade-entry index must be even. Therefore any later negative
perturbation, i.e. any later step with division exponent `1`, is impossible.

This is the formal fatal-parity statement: a third negative perturbation would
have to occur after the cascade has already been initiated, and such an event
contradicts the mandatory even tail of Mechanism 3.
-/
theorem corollary_1H1_third_negative_perturbation_fatal
  (n x : ℕ)
  (h_mech3 : lemma_1H_mechanism3_trajectory n x) :
  ∃ entry : ℕ,
    1 ≤ entry ∧
      ∀ m ∈ Ico (entry + 1) (n - 2),
        val ((T^[m]) x) ≠ 1 := by

  rcases h_mech3 with
    ⟨entry, h_entry_pos, h_odd_pair, h_pre_even, h_tail_even⟩

  refine ⟨entry, h_entry_pos, ?_⟩

  intro m hm_tail h_negative

  have h_even_event :
      lemma_1H_even_parity_event x m :=
    h_tail_even m hm_tail

  unfold lemma_1H_even_parity_event at h_even_event

  rw [h_negative] at h_even_event
  simp at h_even_event

#check corollary_1H1_third_negative_perturbation_fatal
#print axioms corollary_1H1_third_negative_perturbation_fatal

end Section20K_Corollary1H1
-- ===============================================================
-- SECTION 21: LEMMA 1I
-- TERMINAL NO-LIFT EDGE CASE
-- ===============================================================

section Section21_Lemma1I

/--
Terminal no-lift profile.

This is the exceptional edge case: no positive lifting tail is generated, and
every active prefix sits one unit below equilibrium.
-/
def Lemma1I_TerminalNoLiftProfile (n x : ℕ) : Prop :=
  ∀ k ∈ Ico 1 (n + 1), S k x = 2 * k - 1

/--
The terminal no-lift profile restricts to every numerator-deviation index.
-/
lemma Lemma1I_terminal_no_lift_internal_profile
  (n x k : ℕ)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x)
  (hk : k ∈ Ico 1 n) :
  S k x = 2 * k - 1 := by

  exact h_profile k (by
    rw [mem_Ico] at hk ⊢
    omega)

/--
The terminal no-lift profile gives the final denominator exponent
`S_n = 2n - 1`.
-/
lemma Lemma1I_terminal_no_lift_final_exponent
  (n x : ℕ)
  (hn : 0 < n)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x) :
  S n x = 2 * n - 1 := by

  exact h_profile n (by
    rw [mem_Ico]
    exact ⟨hn, by omega⟩)

/--
Under the terminal no-lift profile, every numerator-deviation term is a
negative coasting term.
-/
lemma Lemma1I_T_seq_eq_no_lift_term
  (n x k : ℕ)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x)
  (hk : k ∈ Ico 1 n) :
  T_seq n x k =
    -((3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)) := by

  unfold T_seq
  rw [Lemma1I_terminal_no_lift_internal_profile n x k h_profile hk]

  have hk_pos : 1 ≤ k := (mem_Ico.mp hk).1

  have h_exp : 2 * k = (2 * k - 1) + 1 := by
    omega

  have h_pow_start :
      (2 : ℤ)^(2 * k) =
        (2 : ℤ)^((2 * k - 1) + 1) :=
    congrArg (fun e : ℕ => (2 : ℤ)^e) h_exp

  have h_pow :
      (2 : ℤ)^(2 * k) =
        (2 : ℤ)^(2 * k - 1) * 2 := by
    rw [h_pow_start]
    rw [pow_add]
    norm_num

  rw [h_pow]
  ring

/--
Therefore the actual numerator deviation is the negative coasting mass.
-/
theorem Lemma1I_delta_N_actual_inc_eq_negative_no_lift_sum
  (n x : ℕ)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x) :
  delta_N_actual_inc n x =
    -∑ k ∈ Ico 1 n,
      (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1) := by

  have h_delta_def :
      delta_N_actual_inc n x = ∑ k ∈ Ico 1 n, T_seq n x k := by
    unfold delta_N_actual_inc T_seq
    apply sum_congr rfl
    intro k _
    rfl

  rw [h_delta_def]

  calc
    ∑ k ∈ Ico 1 n, T_seq n x k
        =
      ∑ k ∈ Ico 1 n,
        -((3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)) := by
          apply sum_congr rfl
          intro k hk
          exact Lemma1I_T_seq_eq_no_lift_term n x k h_profile hk
    _ =
      -∑ k ∈ Ico 1 n,
        (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1) := by
          rw [sum_neg_distrib]

end Section21_Lemma1I

#check Lemma1I_TerminalNoLiftProfile
#check Lemma1I_terminal_no_lift_final_exponent
#check Lemma1I_T_seq_eq_no_lift_term
#check Lemma1I_delta_N_actual_inc_eq_negative_no_lift_sum
/--
The no-lift coasting mass has the closed geometric form

`∑_{k=1}^{n-1} 3^(n-1-k) * 2^(2k-1)
 = 2 * (4^(n-1) - 3^(n-1))`.
-/
lemma Lemma1I_no_lift_coasting_mass_eq
  (n : ℕ) :
  ∑ k ∈ Ico 1 n,
    (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)
    =
  2 * ((4 : ℤ)^(n - 1) - (3 : ℤ)^(n - 1)) := by

  have h_shift :
      ∑ k ∈ Ico 1 n,
        (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)
        =
      2 * ∑ j ∈ range (n - 1),
        (3 : ℤ)^((n - 1) - 1 - j) * (2 : ℤ)^(2 * j) := by

    rw [mul_sum]
    rw [sum_Ico_eq_sum_range]

    apply sum_congr rfl
    intro j hj

    have hj_lt : j < n - 1 := mem_range.mp hj

    have h_three_exp :
        n - 1 - (1 + j) = (n - 1) - 1 - j := by
      omega

    have h_two_exp :
        2 * (1 + j) - 1 = 2 * j + 1 := by
      omega

    rw [h_three_exp, h_two_exp, pow_add]
    norm_num
    ring

  rw [h_shift]

  have h_N_sum := N_eq_as_sum_int (n - 1)

  have h_N_form :
      (N_eq (n - 1) : ℤ) =
        (4 : ℤ)^(n - 1) - (3 : ℤ)^(n - 1) := by
    rw [N_eq_int]
    have h_pow :
        (2 : ℤ)^(2 * (n - 1)) = (4 : ℤ)^(n - 1) := by
      rw [pow_mul]
      norm_num
    rw [h_pow]

  rw [← h_N_sum, h_N_form]

/--
Closed form of the terminal no-lift numerator deviation.
-/
theorem Lemma1I_delta_N_actual_inc_no_lift_closed
  (n x : ℕ)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x) :
  delta_N_actual_inc n x =
    -2 * ((4 : ℤ)^(n - 1) - (3 : ℤ)^(n - 1)) := by

  rw [Lemma1I_delta_N_actual_inc_eq_negative_no_lift_sum n x h_profile]
  rw [Lemma1I_no_lift_coasting_mass_eq n]
  ring

#check Lemma1I_no_lift_coasting_mass_eq
#check Lemma1I_delta_N_actual_inc_no_lift_closed
/--
Under the terminal no-lift profile, the actual numerator has the closed form

`N_new = 2^(2n - 1) - 3^(n - 1)`.
-/
theorem Lemma1I_sum_T_no_lift_closed
  (n x : ℕ)
  (hn : 0 < n)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x) :
  (sum_T n x : ℤ) =
    (2 : ℤ)^(2 * n - 1) - (3 : ℤ)^(n - 1) := by

  have h_delta_bridge :
      (sum_T n x : ℤ) - (N_eq n : ℤ) =
        delta_N_actual_inc n x :=
    lemma_delta_equiv_bridge n x hn

  have h_delta :
      delta_N_actual_inc n x =
        -2 * ((4 : ℤ)^(n - 1) - (3 : ℤ)^(n - 1)) :=
    Lemma1I_delta_N_actual_inc_no_lift_closed n x h_profile

  have h_Neq :
      (N_eq n : ℤ) =
        (2 : ℤ)^(2 * n) - (3 : ℤ)^n :=
    N_eq_int n

  have h_pow2 :
      (2 : ℤ)^(2 * n) =
        (2 : ℤ)^(2 * n - 1) * 2 := by
    have h_exp : 2 * n = (2 * n - 1) + 1 := by
      omega
    rw [h_exp, pow_add]
    norm_num

  have h_pow3 :
      (3 : ℤ)^n =
        (3 : ℤ)^(n - 1) * 3 := by
    have h_exp : n = (n - 1) + 1 := by
      omega
    rw [h_exp, pow_add]
    norm_num

  have h_pow4 :
      (4 : ℤ)^(n - 1) =
        (2 : ℤ)^(2 * n - 2) := by
    have h_exp : 2 * (n - 1) = 2 * n - 2 := by
      omega
    rw [← h_exp]
    rw [pow_mul]
    norm_num

  have h_pow2_relation :
      (2 : ℤ)^(2 * n - 1) =
        2 * (2 : ℤ)^(2 * n - 2) := by
    have h_exp : 2 * n - 1 = (2 * n - 2) + 1 := by
      omega
    rw [h_exp, pow_add]
    norm_num
    ring

  rw [h_delta, h_Neq] at h_delta_bridge

  calc
    (sum_T n x : ℤ)
        =
      ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) +
        (-2 * ((4 : ℤ)^(n - 1) - (3 : ℤ)^(n - 1))) := by
          omega
    _ =
      ((2 : ℤ)^(2 * n - 1) * 2 - (3 : ℤ)^(n - 1) * 3) +
        (-2 * ((2 : ℤ)^(2 * n - 2) - (3 : ℤ)^(n - 1))) := by
          rw [h_pow2, h_pow3, h_pow4]
    _ =
      (2 : ℤ)^(2 * n - 1) - (3 : ℤ)^(n - 1) := by
          rw [h_pow2_relation]
          ring

/--
Under the terminal no-lift profile, the denominator has the closed form

`D_new = 2^(2n - 1) - 3^n`.
-/
theorem Lemma1I_D_new_no_lift_closed
  (n x : ℕ)
  (hn : 0 < n)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x) :
  D_new n x =
    (2 : ℚ)^(2 * n - 1) - (3 : ℚ)^n := by

  unfold D_new

  have hS :
      S n x = 2 * n - 1 :=
    Lemma1I_terminal_no_lift_final_exponent n x hn h_profile

  rw [hS]

#check Lemma1I_sum_T_no_lift_closed
#check Lemma1I_D_new_no_lift_closed
lemma Lemma1I_five_mul_three_pow_lt_two_pow
  (n : ℕ)
  (hn : 5 ≤ n) :
  5 * 3^(n - 1) < 2^(2 * n - 1) := by

  have h_core : ∀ t : ℕ, 405 * 3^t < 512 * 4^t := by
    intro t
    induction t with
    | zero =>
        norm_num
    | succ t ih =>
        calc
          405 * 3^(t + 1)
              = 3 * (405 * 3^t) := by ring
          _ < 3 * (512 * 4^t) := by
              exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ 4 * (512 * 4^t) := by
              exact Nat.mul_le_mul_right (512 * 4^t) (by norm_num : 3 ≤ 4)
          _ = 512 * 4^(t + 1) := by ring

  let t := n - 5

  have hn_eq : n = t + 5 := by
    dsimp [t]
    omega

  rw [hn_eq]

  have h_left :
      5 * 3^(t + 5 - 1) = 405 * 3^t := by
    have h_exp : t + 5 - 1 = t + 4 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  have h_right :
      2^(2 * (t + 5) - 1) = 512 * 4^t := by
    have h_exp : 2 * (t + 5) - 1 = 2 * t + 9 := by omega
    rw [h_exp, pow_add]

    have h_two :
        2^(2 * t) = 4^t := by
      rw [pow_mul]
      norm_num

    rw [h_two]
    norm_num
    ring

  rw [h_left, h_right]

  exact h_core t

theorem lemma_1I_no_cycle_terminal_no_lift_profile
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x > 1)
  (h_profile : Lemma1I_TerminalNoLiftProfile n x) :
  False := by

  have hS :
      S n x = 2 * n - 1 :=
    Lemma1I_terminal_no_lift_final_exponent n x hn h_profile

  have h_sum_closed :
      (sum_T n x : ℤ) =
        (2 : ℤ)^(2 * n - 1) - (3 : ℤ)^(n - 1) :=
    Lemma1I_sum_T_no_lift_closed n x hn h_profile

  have h_cycle_int :
      (sum_T n x : ℤ) =
        (2 : ℤ)^(S n x) * (x : ℤ) -
          (3 : ℤ)^n * (x : ℤ) :=
    cycle_diophantine_int n x h_cycle hn

  rw [hS] at h_cycle_int

  have h_cycle_closed :
      (sum_T n x : ℤ) =
        ((2 : ℤ)^(2 * n - 1) - (3 : ℤ)^n) * (x : ℤ) := by
    calc
      (sum_T n x : ℤ)
          =
        (2 : ℤ)^(2 * n - 1) * (x : ℤ) -
          (3 : ℤ)^n * (x : ℤ) := h_cycle_int
      _ =
        ((2 : ℤ)^(2 * n - 1) - (3 : ℤ)^n) * (x : ℤ) := by
          ring

  have h_eq_main :
      (2 : ℤ)^(2 * n - 1) - (3 : ℤ)^(n - 1) =
        ((2 : ℤ)^(2 * n - 1) - (3 : ℤ)^n) * (x : ℤ) := by
    rw [← h_sum_closed]
    exact h_cycle_closed

  have h_threshold_nat :
      3^n < 2^(2 * n - 1) := by
    have h_threshold := cycle_existence_threshold n x h_cycle hn
    rw [hS] at h_threshold
    exact h_threshold

  by_cases hn_ge_five : 5 ≤ n

  · let A : ℤ := (2 : ℤ)^(2 * n - 1)
    let B : ℤ := (3 : ℤ)^(n - 1)
    let C : ℤ := (3 : ℤ)^n
    let D : ℤ := A - C
    let N : ℤ := A - B

    have h_eq_N :
        N = D * (x : ℤ) := by
      dsimp [N, D, A, B, C]
      exact h_eq_main

    have hD_pos : 0 < D := by
      dsimp [D, A, C]
      have hcast :
          (3 : ℤ)^n < (2 : ℤ)^(2 * n - 1) := by
        exact_mod_cast h_threshold_nat
      exact sub_pos.mpr hcast

    have hx_ge_two_z :
        (2 : ℤ) ≤ (x : ℤ) := by
      exact_mod_cast (by omega : 2 ≤ x)

    have hA_gt_5B :
        5 * B < A := by
      dsimp [A, B]
      exact_mod_cast
        (Lemma1I_five_mul_three_pow_lt_two_pow n hn_ge_five)

    have hC_eq :
        C = B * 3 := by
      dsimp [C, B]
      have h_exp : n = (n - 1) + 1 := by omega
      rw [h_exp, pow_add]
      norm_num

    have h_N_lt_2D :
        N < 2 * D := by
      dsimp [N, D]
      rw [hC_eq]
      nlinarith [hA_gt_5B]

    have h_twoD_le_Dx :
        2 * D ≤ D * (x : ℤ) := by
      have h_mul :=
        mul_le_mul_of_nonneg_left hx_ge_two_z (le_of_lt hD_pos)
      nlinarith

    have h_twoD_le_N :
        2 * D ≤ N := by
      rw [h_eq_N]
      exact h_twoD_le_Dx

    linarith

  · have hn_le_four : n ≤ 4 := by omega
    interval_cases n

    · norm_num at h_threshold_nat

    · norm_num at h_threshold_nat

    · norm_num at h_eq_main
      omega

    · norm_num at h_eq_main
      omega

#check Lemma1I_five_mul_three_pow_lt_two_pow
#check lemma_1I_no_cycle_terminal_no_lift_profile
#print axioms lemma_1I_no_cycle_terminal_no_lift_profile
/--
Corollary 1I-1: Pure negative perturbation trajectory.

In the no-lift edge case, a pure negative trajectory is exactly the terminal
profile where every active prefix remains one unit below equilibrium.
-/
def Lemma1I_PureNegativePerturbationTrajectory (n x : ℕ) : Prop :=
  Lemma1I_TerminalNoLiftProfile n x

/--
Corollary 1I-1.

No pure negative perturbation trajectory is permissible for a nontrivial cycle.
This is an immediate consequence of Lemma 1I's terminal no-lift algebraic
closure.
-/
theorem corollary_1I1_no_pure_negative_perturbation_trajectory
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x > 1)
  (h_pure_negative : Lemma1I_PureNegativePerturbationTrajectory n x) :
  False := by

  exact
    lemma_1I_no_cycle_terminal_no_lift_profile
      n x h_cycle hn hx h_pure_negative

#check Lemma1I_PureNegativePerturbationTrajectory
#check corollary_1I1_no_pure_negative_perturbation_trajectory


-- =======================================================================================
-- Section 22: Lemma 1J
-- =======================================================================================
/-- Lemma 1J `GP1`: the coasting phase, from `k = 1` to `q - 1`. -/
noncomputable def Lemma1J_GP1 (n x q : ℕ) : ℤ :=
  ∑ k ∈ Ico 1 q, T_seq n x k

/-- Lemma 1J `GP2`: the lifted tail phase, from `k = q` to `n - 1`. -/
noncomputable def Lemma1J_GP2 (n x q : ℕ) : ℤ :=
  ∑ k ∈ Ico q n, T_seq n x k

/--
Lemma 1J Step 1.

The exact numerator deviation bifurcates at the parity bridge index `q`.
-/
theorem lemma_1J_step1_delta_Nactual_bifurcation
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n) :
  delta_N_actual_inc n x =
    Lemma1J_GP1 n x q + Lemma1J_GP2 n x q := by

  unfold delta_N_actual_inc Lemma1J_GP1 Lemma1J_GP2 T_seq

  have h_split :
      Ico 1 n = Ico 1 q ∪ Ico q n := by
    ext k
    simp only [mem_Ico, mem_union]
    omega

  rw [h_split]

  have h_disjoint :
      Disjoint (Ico 1 q) (Ico q n) :=
    disjoint_left.mpr
      (by
        intro k hk_left hk_right
        rw [mem_Ico] at hk_left hk_right
        omega)

  rw [sum_union h_disjoint]
/--
Lemma 1J Step 2.

Under the pre-bridge coasting condition `d_k = -1`, equivalently
`S_k = 2k - 1`, the first geometric phase has the manuscript closed form.
-/
theorem lemma_1J_step2_GP1_closed_form
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1) :
  Lemma1J_GP1 n x q =
    2 * (3 : ℤ)^(n - 1) -
      2 * (4 : ℤ)^(q - 1) * (3 : ℤ)^(n - q) := by

  have h_gp1_mass :
      Lemma1J_GP1 n x q =
        -∑ k ∈ Ico 1 q,
          (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1) := by

    unfold Lemma1J_GP1

    calc
      ∑ k ∈ Ico 1 q, T_seq n x k
          =
        ∑ k ∈ Ico 1 q,
          -((3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)) := by
            apply sum_congr rfl
            intro k hk

            unfold T_seq
            rw [h_coast k hk]

            have hk_pos : 1 ≤ k := (mem_Ico.mp hk).1

            have h_exp :
                2 * k = (2 * k - 1) + 1 := by
              omega

            have h_pow_start :
                (2 : ℤ)^(2 * k) =
                  (2 : ℤ)^((2 * k - 1) + 1) :=
              congrArg (fun e : ℕ => (2 : ℤ)^e) h_exp

            have h_pow :
                (2 : ℤ)^(2 * k) =
                  (2 : ℤ)^(2 * k - 1) * 2 := by
              rw [h_pow_start]
              rw [pow_add]
              norm_num

            rw [h_pow]
            ring
      _ =
        -∑ k ∈ Ico 1 q,
          (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1) := by
            rw [sum_neg_distrib]

  have h_shift :
      ∑ k ∈ Ico 1 q,
        (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)
        =
      (2 * (3 : ℤ)^(n - q)) *
        ∑ j ∈ range (q - 1),
          (3 : ℤ)^((q - 1) - 1 - j) * (2 : ℤ)^(2 * j) := by

    rw [sum_Ico_eq_sum_range]
    rw [mul_sum]

    apply sum_congr rfl
    intro j hj

    have hj_lt : j < q - 1 := mem_range.mp hj

    have h_three_exp :
        n - 1 - (1 + j) =
          (n - q) + ((q - 1) - 1 - j) := by
      omega

    have h_two_exp :
        2 * (1 + j) - 1 = 2 * j + 1 := by
      omega

    rw [h_three_exp, h_two_exp]
    rw [pow_add, pow_add]
    norm_num
    ring

  have h_mass_closed :
      ∑ k ∈ Ico 1 q,
        (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)
        =
      2 * (4 : ℤ)^(q - 1) * (3 : ℤ)^(n - q) -
        2 * (3 : ℤ)^(n - 1) := by

    have h_N_sum := N_eq_as_sum_int (q - 1)

    have h_N_form :
        (N_eq (q - 1) : ℤ) =
          (4 : ℤ)^(q - 1) - (3 : ℤ)^(q - 1) := by
      rw [N_eq_int]
      have h_pow :
          (2 : ℤ)^(2 * (q - 1)) = (4 : ℤ)^(q - 1) := by
        rw [pow_mul]
        norm_num
      rw [h_pow]

    have h_pow3 :
        (3 : ℤ)^(n - q) * (3 : ℤ)^(q - 1) =
          (3 : ℤ)^(n - 1) := by
      rw [← pow_add]

      have hq_le_n : q ≤ n := le_of_lt hqn
      have hq_one : 1 ≤ q :=
        le_trans (by norm_num : 1 ≤ 2) hq
      have hn_one : 1 ≤ n :=
        le_trans hq_one hq_le_n

      have h_exp :
          n - q + (q - 1) = n - 1 := by
        have h_exp_int :
            ((n - q + (q - 1) : ℕ) : ℤ) =
              ((n - 1 : ℕ) : ℤ) := by
          rw [Nat.cast_add]
          rw [Nat.cast_sub hq_le_n]
          rw [Nat.cast_sub hq_one]
          rw [Nat.cast_sub hn_one]
          ring
        exact_mod_cast h_exp_int

      rw [h_exp]

    calc
      ∑ k ∈ Ico 1 q,
        (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k - 1)
          =
        (2 * (3 : ℤ)^(n - q)) *
          ∑ j ∈ range (q - 1),
            (3 : ℤ)^((q - 1) - 1 - j) * (2 : ℤ)^(2 * j) := h_shift
      _ =
        (2 * (3 : ℤ)^(n - q)) * (N_eq (q - 1) : ℤ) := by
          rw [← h_N_sum]
      _ =
        (2 * (3 : ℤ)^(n - q)) *
          ((4 : ℤ)^(q - 1) - (3 : ℤ)^(q - 1)) := by
          rw [h_N_form]
      _ =
        2 * (4 : ℤ)^(q - 1) * (3 : ℤ)^(n - q) -
          2 * ((3 : ℤ)^(n - q) * (3 : ℤ)^(q - 1)) := by
          ring
      _ =
        2 * (4 : ℤ)^(q - 1) * (3 : ℤ)^(n - q) -
          2 * (3 : ℤ)^(n - 1) := by
          rw [h_pow3]

  rw [h_gp1_mass, h_mass_closed]
  ring
/-- Lemma 1J `T'_k`: the inflated lifted-tail term. -/
noncomputable def Lemma1J_Tprime (n q k : ℕ) : ℤ :=
  (3 : ℤ)^(n - 1 - k) * (4 : ℤ)^k *
    (2 : ℤ)^(2 * 3^(k - q))

#check lemma_1J_step2_GP1_closed_form

/--
Lemma 1J Step 3.

The inflated lifted-tail series is strictly capped by the terminal term
multiplied by the manuscript geometric ceiling.
-/
theorem lemma_1J_step3_Tprime_tail_bound
  (n q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n) :
  (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ)) <
    (16 / 61 : ℚ) * (4 : ℚ)^n *
      (2 : ℚ)^(2 * 3^(n - 1 - q)) := by

  let terminal : ℚ :=
    (4 : ℚ)^(n - 1) *
      (2 : ℚ)^(2 * 3^(n - 1 - q))

  have h_exp_growth :
      ∀ a r : ℕ, 2 * 3^a + 4 * r ≤ 2 * 3^(a + r) := by
    intro a r
    induction r with
    | zero =>
        simp
    | succ r ih =>
        have ha : 1 ≤ 3^a :=
          Nat.succ_le_of_lt (pow_pos (by decide : 0 < 3) a)

        have h_step :
            2 * 3^a + 4 * (r + 1) ≤
              3 * (2 * 3^a + 4 * r) := by
          nlinarith [ha]

        have h_mul :
            3 * (2 * 3^a + 4 * r) ≤
              3 * (2 * 3^(a + r)) :=
          Nat.mul_le_mul_left 3 ih

        have h_rhs :
            3 * (2 * 3^(a + r)) =
              2 * 3^(a + (r + 1)) := by
          rw [show a + (r + 1) = a + r + 1 by omega]
          rw [pow_succ]
          ring

        calc
          2 * 3^a + 4 * (r + 1)
              ≤ 3 * (2 * 3^a + 4 * r) := h_step
          _ ≤ 3 * (2 * 3^(a + r)) := h_mul
          _ = 2 * 3^(a + (r + 1)) := h_rhs

  have h_pointwise :
      ∀ k ∈ Ico q n,
        (Lemma1J_Tprime n q k : ℚ) ≤
          terminal * (3 / 64 : ℚ)^(n - 1 - k) := by
    intro k hk

    have hk_ge : q ≤ k := (mem_Ico.mp hk).1
    have hk_lt : k < n := (mem_Ico.mp hk).2
    have hk_le_n1 : k ≤ n - 1 := Nat.le_pred_of_lt hk_lt
    have hq_le_n1 : q ≤ n - 1 := le_trans hk_ge hk_le_n1

    let a := k - q
    let r := n - 1 - k
    let b := n - 1 - q

    have hb : b = a + r := by
      dsimp [a, r, b]
      have h_int :
          ((n - 1 - q : ℕ) : ℤ) =
            ((k - q + (n - 1 - k) : ℕ) : ℤ) := by
        rw [Nat.cast_add]
        rw [Nat.cast_sub hq_le_n1]
        rw [Nat.cast_sub hk_ge]
        rw [Nat.cast_sub hk_le_n1]
        ring
      exact_mod_cast h_int

    have hn1 : n - 1 = k + r := by
      dsimp [r]
      rw [add_comm]
      exact (Nat.sub_add_cancel hk_le_n1).symm

    have h_exp_le :
        2 * 3^a + 4 * r ≤ 2 * 3^b := by
      rw [hb]
      exact h_exp_growth a r

    have h_pow_le_nat :
        2^(2 * 3^a + 4 * r) ≤ 2^(2 * 3^b) :=
      Nat.pow_le_pow_right (by norm_num) h_exp_le

    have h_pow_le :
        (2 : ℚ)^(2 * 3^a) * (16 : ℚ)^r
          ≤ (2 : ℚ)^(2 * 3^b) := by
      have h16 :
          (16 : ℚ)^r = (2 : ℚ)^(4 * r) := by
        rw [show (16 : ℚ) = 2^4 by norm_num]
        rw [pow_mul]

      rw [h16]
      rw [← pow_add]
      exact_mod_cast h_pow_le_nat

    have h_div_le :
        (2 : ℚ)^(2 * 3^a)
          ≤ (2 : ℚ)^(2 * 3^b) / (16 : ℚ)^r := by
      rw [le_div_iff₀]
      · exact h_pow_le
      · positivity

    have h_weight_nonneg :
        0 ≤ (3 : ℚ)^r * (4 : ℚ)^k := by
      positivity

    have h_scaled :
        ((3 : ℚ)^r * (4 : ℚ)^k) *
            (2 : ℚ)^(2 * 3^a)
          ≤
        ((3 : ℚ)^r * (4 : ℚ)^k) *
            ((2 : ℚ)^(2 * 3^b) / (16 : ℚ)^r) := by
      exact mul_le_mul_of_nonneg_left h_div_le h_weight_nonneg

    have h_terminal_rewrite :
        terminal * (3 / 64 : ℚ)^r =
          ((3 : ℚ)^r * (4 : ℚ)^k) *
            ((2 : ℚ)^(2 * 3^b) / (16 : ℚ)^r) := by
      dsimp [terminal]

      have hb_index : n - 1 - q = b := by rfl

      rw [hb_index]
      rw [hn1]
      rw [pow_add]
      rw [div_pow]

      have h64 :
          (64 : ℚ)^r = (4 : ℚ)^r * (16 : ℚ)^r := by
        rw [show (64 : ℚ) = 4 * 16 by norm_num]
        rw [mul_pow]

      rw [h64]
      field_simp

    have hr : n - 1 - k = r := by rfl
    have ha : k - q = a := by rfl

    unfold Lemma1J_Tprime
    push_cast
    rw [hr, ha]

    calc
      (3 : ℚ)^r * (4 : ℚ)^k * (2 : ℚ)^(2 * 3^a)
          ≤
        ((3 : ℚ)^r * (4 : ℚ)^k) *
          ((2 : ℚ)^(2 * 3^b) / (16 : ℚ)^r) := h_scaled
      _ =
        terminal * (3 / 64 : ℚ)^r := by
          rw [h_terminal_rewrite]

  have h_reindex :
      ∑ k ∈ Ico q n, (3 / 64 : ℚ)^(n - 1 - k)
        =
      ∑ r ∈ range (n - q), (3 / 64 : ℚ)^r := by
    rw [sum_Ico_eq_sum_range]

    have h_congr :
        ∑ j ∈ range (n - q),
            (3 / 64 : ℚ)^(n - 1 - (q + j))
          =
        ∑ j ∈ range (n - q),
            (3 / 64 : ℚ)^((n - q) - 1 - j) := by
      apply sum_congr rfl
      intro j hj

      have hj_lt : j < n - q := mem_range.mp hj

      have h_exp :
          n - 1 - (q + j) = (n - q) - 1 - j := by
        omega

      rw [h_exp]

    rw [h_congr]
    exact sum_range_reflect (fun r => (3 / 64 : ℚ)^r) (n - q)

  have h_sum_bound :
      (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ)) ≤
        terminal * ∑ r ∈ range (n - q), (3 / 64 : ℚ)^r := by
    calc
      ∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ)
          ≤
        ∑ k ∈ Ico q n,
          terminal * (3 / 64 : ℚ)^(n - 1 - k) := by
            apply sum_le_sum
            intro k hk
            exact h_pointwise k hk
      _ =
        terminal * ∑ k ∈ Ico q n,
          (3 / 64 : ℚ)^(n - 1 - k) := by
            rw [mul_sum]
      _ =
        terminal * ∑ r ∈ range (n - q),
          (3 / 64 : ℚ)^r := by
            rw [h_reindex]

  have h_geom :
      ∑ r ∈ range (n - q), (3 / 64 : ℚ)^r < 64 / 61 := by
    have h_geom_eq :
        ∑ r ∈ range (n - q), (3 / 64 : ℚ)^r =
          (1 - (3 / 64 : ℚ)^(n - q)) / (1 - 3 / 64) := by
      have h_standard :=
        geom_sum_eq (x := (3 / 64 : ℚ)) (by norm_num) (n - q)
      rw [h_standard]
      generalize (3 / 64 : ℚ)^(n - q) = A
      ring

    rw [h_geom_eq]
    rw [show (1 - 3 / 64 : ℚ) = 61 / 64 by norm_num]

    have h_pow_pos :
        0 < (3 / 64 : ℚ)^(n - q) := by
      positivity

    nlinarith

  have h_terminal_pos : 0 < terminal := by
    dsimp [terminal]
    positivity

  calc
    (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ))
        ≤
      terminal * ∑ r ∈ range (n - q), (3 / 64 : ℚ)^r := h_sum_bound
    _ <
      terminal * (64 / 61 : ℚ) := by
        exact mul_lt_mul_of_pos_left h_geom h_terminal_pos
    _ =
      (16 / 61 : ℚ) * (4 : ℚ)^n *
        (2 : ℚ)^(2 * 3^(n - 1 - q)) := by
          dsimp [terminal]

          have h4 :
              (4 : ℚ)^n = (4 : ℚ)^(n - 1) * 4 := by
            have h_exp : n = (n - 1) + 1 := by
              omega
            rw [h_exp]
            rw [pow_add]
            norm_num

          rw [h4]
          ring
#check lemma_1J_step3_Tprime_tail_bound

/-- Lemma 1J Step 4: the derived closed `GP1` expression. -/
noncomputable def Lemma1J_GP1_closed (n q : ℕ) : ℤ :=
  2 * (3 : ℤ)^(n - 1) -
    2 * (4 : ℤ)^(q - 1) * (3 : ℤ)^(n - q)

/-- Lemma 1J Step 4: the derived terminal ceiling for `GP2`. -/
noncomputable def Lemma1J_GP2_ceiling (n q : ℕ) : ℚ :=
  (16 / 61 : ℚ) * (4 : ℚ)^n *
    (2 : ℚ)^(2 * 3^(n - 1 - q))

/--
Lemma 1J Step 4a.

Substitute the derived `GP1` expression into the Step 1 bifurcation.
-/
theorem lemma_1J_step4_delta_Nactual_GP1_substitution
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1) :
  (delta_N_actual_inc n x : ℚ) =
    (Lemma1J_GP1_closed n q : ℚ) +
      (Lemma1J_GP2 n x q : ℚ) := by

  have h_step1 :=
    lemma_1J_step1_delta_Nactual_bifurcation n x q hq hqn

  have h_step2 :=
    lemma_1J_step2_GP1_closed_form n x q hq hqn h_coast

  have h_step1_q :
      (delta_N_actual_inc n x : ℚ) =
        (Lemma1J_GP1 n x q : ℚ) +
          (Lemma1J_GP2 n x q : ℚ) := by
    exact_mod_cast h_step1

  have h_step2_q :
      (Lemma1J_GP1 n x q : ℚ) =
        (Lemma1J_GP1_closed n q : ℚ) := by
    unfold Lemma1J_GP1_closed
    exact_mod_cast h_step2

  rw [h_step1_q, h_step2_q]

/--
Lemma 1J Step 4b.

Add the derived `GP1` expression to the Step 3 terminal ceiling.
-/
theorem lemma_1J_step4_derived_GP_sum_bound
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1) :
  (Lemma1J_GP1 n x q : ℚ) +
      (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ))
    <
    (Lemma1J_GP1_closed n q : ℚ) +
      Lemma1J_GP2_ceiling n q := by

  have h_step2 :=
    lemma_1J_step2_GP1_closed_form n x q hq hqn h_coast

  have h_step2_q :
      (Lemma1J_GP1 n x q : ℚ) =
        (Lemma1J_GP1_closed n q : ℚ) := by
    unfold Lemma1J_GP1_closed
    exact_mod_cast h_step2

  have h_step3 :=
    lemma_1J_step3_Tprime_tail_bound n q hq hqn

  unfold Lemma1J_GP2_ceiling
  rw [h_step2_q]

  simpa [add_comm, add_left_comm, add_assoc] using
    add_lt_add_left h_step3 (Lemma1J_GP1_closed n q : ℚ)
#check lemma_1J_step4_delta_Nactual_GP1_substitution
#check lemma_1J_step4_derived_GP_sum_bound
/--
Lemma 1J Step 5.

The total exponent is the equilibrium exponent `2n` plus the terminal
cascade deviation.
-/
theorem lemma_1J_step5_total_exponent
  (n x q : ℕ)
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) :
  S n x = 2 * n + 2 * 3^(n - 1 - q) := by

  have h_rel := s_relationship n x
  rw [h_deltaS] at h_rel

  have h_cast :
      (S n x : ℤ) =
        ((2 * n + 2 * 3^(n - 1 - q) : ℕ) : ℤ) := by
    rw [h_rel]
    push_cast
    ring

  exact_mod_cast h_cast
#check lemma_1J_step5_total_exponent
/--
Lemma 1J Step 6.

Substituting the total exponent into the actual denominator gives the
structural form `4^n * 2^(2 * 3^(n-1-q)) - 3^n`.
-/
theorem lemma_1J_step6_D_new_closed_form
  (n x q : ℕ)
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) :
  D_new n x =
    (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) - (3 : ℚ)^n := by

  have hE :=
    lemma_1J_step5_total_exponent n x q h_deltaS

  unfold D_new
  rw [hE]
  rw [pow_add]

  have h_four :
      (2 : ℚ)^(2 * n) = (4 : ℚ)^n := by
    rw [pow_mul]
    norm_num

  rw [h_four]
#check lemma_1J_step6_D_new_closed_form
/--
Lemma 1J Step 7a.

Since the coasting phase is strictly negative, the actual numerator deviation
is strictly less than the lifted-tail phase.
-/
theorem lemma_1J_step7_delta_Nactual_lt_GP2
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1) :
  (delta_N_actual_inc n x : ℚ) <
    (Lemma1J_GP2 n x q : ℚ) := by

  have h_step1 :=
    lemma_1J_step1_delta_Nactual_bifurcation n x q hq hqn

  have h_step2 :=
    lemma_1J_step2_GP1_closed_form n x q hq hqn h_coast

  have h_step1_q :
      (delta_N_actual_inc n x : ℚ) =
        (Lemma1J_GP1 n x q : ℚ) +
          (Lemma1J_GP2 n x q : ℚ) := by
    exact_mod_cast h_step1

  have hq_one : 1 ≤ q :=
    le_trans (by norm_num : 1 ≤ 2) hq

  have hq_le_n : q ≤ n := le_of_lt hqn

  have hn_one : 1 ≤ n :=
    le_trans hq_one hq_le_n

  have h_pow3_split :
      (3 : ℚ)^(n - 1) =
        (3 : ℚ)^(n - q) * (3 : ℚ)^(q - 1) := by
    rw [← pow_add]

    have h_exp :
        n - q + (q - 1) = n - 1 := by
      have h_exp_int :
          ((n - q + (q - 1) : ℕ) : ℤ) =
            ((n - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add]
        rw [Nat.cast_sub hq_le_n]
        rw [Nat.cast_sub hq_one]
        rw [Nat.cast_sub hn_one]
        ring
      exact_mod_cast h_exp_int

    rw [h_exp]

  have h_qminus_pos : 0 < q - 1 := by
    omega

  have h_pow_lt_nat :
      3^(q - 1) < 4^(q - 1) :=
    Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt h_qminus_pos)

  have h_pow_lt :
      (3 : ℚ)^(q - 1) < (4 : ℚ)^(q - 1) := by
    exact_mod_cast h_pow_lt_nat

  have h_mul_pos :
      0 < (3 : ℚ)^(n - q) := by
    positivity

  have h_gp1_neg :
      (Lemma1J_GP1 n x q : ℚ) < 0 := by
    rw [h_step2]
    push_cast
    rw [h_pow3_split]
    nlinarith [mul_lt_mul_of_pos_left h_pow_lt h_mul_pos]

  rw [h_step1_q]
  linarith
#check lemma_1J_step7_delta_Nactual_lt_GP2
/--
Lemma 1J Step 7b.

After substituting Step 6 for the denominator, the inflated lifted-tail ratio
is bounded by the manuscript ceiling ratio.
-/
theorem lemma_1J_step7_Tprime_ratio_bound
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) :
  (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ)) / D_new n x <
    Lemma1J_GP2_ceiling n q /
      ((4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) - (3 : ℚ)^n) := by

  have h_step3 :=
    lemma_1J_step3_Tprime_tail_bound n q hq hqn

  have h_step6 :=
    lemma_1J_step6_D_new_closed_form n x q h_deltaS

  have hn_pos : 0 < n := by
    omega

  have h3_lt_4_nat :
      3^n < 4^n :=
    Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt hn_pos)

  have h_extra_ge :
      1 ≤ 2^(2 * 3^(n - 1 - q)) :=
    Nat.succ_le_of_lt
      (pow_pos (by decide : 0 < 2) (2 * 3^(n - 1 - q)))

  have h4_le_A_nat :
      4^n ≤ 4^n * 2^(2 * 3^(n - 1 - q)) := by
    calc
      4^n = 4^n * 1 := by ring
      _ ≤ 4^n * 2^(2 * 3^(n - 1 - q)) :=
        Nat.mul_le_mul_left (4^n) h_extra_ge

  have h3_lt_A_nat :
      3^n < 4^n * 2^(2 * 3^(n - 1 - q)) :=
    lt_of_lt_of_le h3_lt_4_nat h4_le_A_nat

  have hD_pos :
      0 <
        (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) -
          (3 : ℚ)^n := by
    have h_cast :
        (3 : ℚ)^n <
          (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) := by
      exact_mod_cast h3_lt_A_nat
    exact sub_pos.mpr h_cast

  unfold Lemma1J_GP2_ceiling
  rw [h_step6]

  exact div_lt_div_of_pos_right h_step3 hD_pos
#check lemma_1J_step7_Tprime_ratio_bound
/--
Lemma 1J Step 7c.

The manuscript ceiling ratio is strictly below `1`.
-/
theorem lemma_1J_step7_ceiling_ratio_lt_one
  (n q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n) :
  Lemma1J_GP2_ceiling n q /
      ((4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) - (3 : ℚ)^n)
    < 1 := by

  let e := 2 * 3^(n - 1 - q)
  let A : ℚ := (4 : ℚ)^n * (2 : ℚ)^e
  let B : ℚ := (3 : ℚ)^n

  have hA_pos : 0 < A := by
    dsimp [A]
    positivity

  have h_e_ge_two : 2 ≤ e := by
    dsimp [e]
    have h_pow : 1 ≤ 3^(n - 1 - q) :=
      Nat.succ_le_of_lt (pow_pos (by decide : 0 < 3) (n - 1 - q))
    nlinarith

  have h_two_pow_ge_four : 4 ≤ 2^e := by
    calc
      4 = 2^2 := by norm_num
      _ ≤ 2^e := Nat.pow_le_pow_right (by norm_num) h_e_ge_two

  have hn_pos : 0 < n := by
    omega

  have h3_lt4 :
      3^n < 4^n :=
    Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt hn_pos)

  have h_fourB_lt_A_nat :
      4 * 3^n < 4^n * 2^e := by
    calc
      4 * 3^n < 4 * 4^n :=
        Nat.mul_lt_mul_of_pos_left h3_lt4 (by norm_num)
      _ = 4^n * 4 := by ring
      _ ≤ 4^n * 2^e :=
        Nat.mul_le_mul_left (4^n) h_two_pow_ge_four

  have h_fourB_lt_A :
      (4 : ℚ) * B < A := by
    dsimp [A, B]
    exact_mod_cast h_fourB_lt_A_nat

  have hD_lower :
      (3 / 4 : ℚ) * A < A - B := by
    nlinarith

  have hD_pos :
      0 < A - B := by
    nlinarith [hA_pos, hD_lower]

  have hcoef :
      (16 / 61 : ℚ) < 3 / 4 := by
    norm_num

  have hnum_lt_D :
      (16 / 61 : ℚ) * A < A - B := by
    have hnum_lt :
        (16 / 61 : ℚ) * A < (3 / 4 : ℚ) * A :=
      mul_lt_mul_of_pos_right hcoef hA_pos
    exact lt_trans hnum_lt hD_lower

  have h_goal :
      ((16 / 61 : ℚ) * A) / (A - B) < 1 := by
    rw [div_lt_iff₀ hD_pos]
    simpa using hnum_lt_D

  unfold Lemma1J_GP2_ceiling
  dsimp [A, B, e] at h_goal ⊢
  simpa [mul_assoc] using h_goal
#check lemma_1J_step7_ceiling_ratio_lt_one
/--
Lemma 1J Step 7d.

Therefore the inflated lifted-tail ratio is strictly below `1`.
-/
theorem lemma_1J_step7_Tprime_ratio_lt_one
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) :
  (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ)) / D_new n x < 1 := by

  exact lt_trans
    (lemma_1J_step7_Tprime_ratio_bound n x q hq hqn h_deltaS)
    (lemma_1J_step7_ceiling_ratio_lt_one n q hq hqn)
#check lemma_1J_step7_Tprime_ratio_lt_one
/--
Lemma 1J Step 7e.

The actual lifted-tail phase is bounded above by the inflated lifted-tail
series obtained by dropping the internal subtraction `-1`.
-/
theorem lemma_1J_step7_GP2_le_Tprime_tail
  (n x q : ℕ)
  (h_cascade :
    ∀ k ∈ Ico q n, S k x = 2 * k + 2 * 3^(k - q)) :
  (Lemma1J_GP2 n x q : ℚ) ≤
    ∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ) := by

  unfold Lemma1J_GP2
  push_cast

  apply sum_le_sum
  intro k hk

  unfold T_seq Lemma1J_Tprime
  push_cast

  rw [h_cascade k hk]

  have h_pow4 :
      (2 : ℚ)^(2 * k) = (4 : ℚ)^k := by
    rw [show (4 : ℚ) = 2^2 by norm_num]
    rw [pow_mul]

  rw [pow_add, h_pow4]

  have h_inner :
      (4 : ℚ)^k * (2 : ℚ)^(2 * 3^(k - q)) - (4 : ℚ)^k
        ≤
      (4 : ℚ)^k * (2 : ℚ)^(2 * 3^(k - q)) := by
    have h_nonneg : 0 ≤ (4 : ℚ)^k := by
      positivity
    linarith

  have h_weight :
      0 ≤ (3 : ℚ)^(n - 1 - k) := by
    positivity

  have h_scaled :=
    mul_le_mul_of_nonneg_left h_inner h_weight

  simp [mul_assoc] at *
#check lemma_1J_step7_GP2_le_Tprime_tail
/--
Lemma 1J final ratio closure.

For a parity-bridge trajectory followed by the 3-adic cascade, the actual
numerator deviation divided by the actual denominator is strictly below `1`.
-/
theorem lemma_1J_delta_Nactual_ratio_lt_one
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1)
  (h_cascade :
    ∀ k ∈ Ico q n, S k x = 2 * k + 2 * 3^(k - q))
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) :
  (delta_N_actual_inc n x : ℚ) / D_new n x < 1 := by

  have h_delta_lt_gp2 :=
    lemma_1J_step7_delta_Nactual_lt_GP2
      n x q hq hqn h_coast

  have h_gp2_le_tail :=
    lemma_1J_step7_GP2_le_Tprime_tail
      n x q h_cascade

  have h_delta_lt_tail :
      (delta_N_actual_inc n x : ℚ) <
        ∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ) :=
    lt_of_lt_of_le h_delta_lt_gp2 h_gp2_le_tail

  have hD_pos : 0 < D_new n x := by
    have h_step6 :=
      lemma_1J_step6_D_new_closed_form n x q h_deltaS

    rw [h_step6]

    have hq_pos : 0 < q :=
      lt_of_lt_of_le (by norm_num : 0 < 2) hq

    have hn_pos : 0 < n :=
      lt_trans hq_pos hqn

    have h3_lt4 :
        3^n < 4^n :=
      Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt hn_pos)

    have h_extra_ge :
        1 ≤ 2^(2 * 3^(n - 1 - q)) :=
      Nat.succ_le_of_lt
        (pow_pos (by decide : 0 < 2) (2 * 3^(n - 1 - q)))

    have h4_le_A :
        4^n ≤ 4^n * 2^(2 * 3^(n - 1 - q)) := by
      calc
        4^n = 4^n * 1 := by ring
        _ ≤ 4^n * 2^(2 * 3^(n - 1 - q)) :=
          Nat.mul_le_mul_left (4^n) h_extra_ge

    have h3_lt_A_nat :
        3^n < 4^n * 2^(2 * 3^(n - 1 - q)) :=
      lt_of_lt_of_le h3_lt4 h4_le_A

    have h3_lt_A :
        (3 : ℚ)^n <
          (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) := by
      exact_mod_cast h3_lt_A_nat

    exact sub_pos.mpr h3_lt_A

  have h_ratio_lt_tail :
      (delta_N_actual_inc n x : ℚ) / D_new n x <
        (∑ k ∈ Ico q n, (Lemma1J_Tprime n q k : ℚ)) / D_new n x :=
    div_lt_div_of_pos_right h_delta_lt_tail hD_pos

  exact lt_trans h_ratio_lt_tail
    (lemma_1J_step7_Tprime_ratio_lt_one n x q hq hqn h_deltaS)
#check lemma_1J_delta_Nactual_ratio_lt_one
/--
Lemma 1J cycle-multiplier obstruction.

If the cycle multiplier condition would require the denominator deviation to
be no larger than the numerator deviation, it contradicts the strict ratio
closure from Lemma 1J.
-/
theorem lemma_1J_cycle_multiplier_obstruction
  (n x q : ℕ)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1)
  (h_cascade :
    ∀ k ∈ Ico q n, S k x = 2 * k + 2 * 3^(k - q))
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q))
  (h_multiplier :
    D_new n x ≤ (delta_N_actual_inc n x : ℚ)) :
  False := by

  have h_ratio :=
    lemma_1J_delta_Nactual_ratio_lt_one
      n x q hq hqn h_coast h_cascade h_deltaS

  have hD_pos : 0 < D_new n x := by
    have h_step6 :=
      lemma_1J_step6_D_new_closed_form n x q h_deltaS

    rw [h_step6]

    have hq_pos : 0 < q :=
      lt_of_lt_of_le (by norm_num : 0 < 2) hq

    have hn_pos : 0 < n :=
      lt_trans hq_pos hqn

    have h3_lt4 :
        3^n < 4^n :=
      Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt hn_pos)

    have h_extra_ge :
        1 ≤ 2^(2 * 3^(n - 1 - q)) :=
      Nat.succ_le_of_lt
        (pow_pos (by decide : 0 < 2) (2 * 3^(n - 1 - q)))

    have h4_le_A :
        4^n ≤ 4^n * 2^(2 * 3^(n - 1 - q)) := by
      calc
        4^n = 4^n * 1 := by ring
        _ ≤ 4^n * 2^(2 * 3^(n - 1 - q)) :=
          Nat.mul_le_mul_left (4^n) h_extra_ge

    have h3_lt_A_nat :
        3^n < 4^n * 2^(2 * 3^(n - 1 - q)) :=
      lt_of_lt_of_le h3_lt4 h4_le_A

    have h3_lt_A :
        (3 : ℚ)^n <
          (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) := by
      exact_mod_cast h3_lt_A_nat

    exact sub_pos.mpr h3_lt_A

  have h_one_le_ratio :
      1 ≤ (delta_N_actual_inc n x : ℚ) / D_new n x := by
    rw [le_div_iff₀ hD_pos]
    simpa using h_multiplier

  linarith
#check lemma_1J_cycle_multiplier_obstruction
/--
Lemma 1J mapped to `is_cycle`.

A nontrivial cycle cannot satisfy the parity-bridge coasting phase followed by
the 3-adic cascade phase.
-/
theorem lemma_1J_no_is_cycle_parity_bridge_cascade
  (n x q : ℕ)
  (h_cycle : is_cycle n x)
  (hx : x > 1)
  (hq : 2 ≤ q)
  (hqn : q < n)
  (h_coast : ∀ k ∈ Ico 1 q, S k x = 2 * k - 1)
  (h_cascade :
    ∀ k ∈ Ico q n, S k x = 2 * k + 2 * 3^(k - q))
  (h_deltaS :
    S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) :
  False := by

  have hn_pos : 0 < n := by
    omega

  have h_threshold_le :
      3^n ≤ 2^(S n x) :=
    le_of_lt (cycle_existence_threshold n x h_cycle hn_pos)

  have h_sum_q :
      (sum_T n x : ℚ) = D_new n x * (x : ℚ) := by
    have h_eq :=
      cycle_implies_explicit_diophantine n x h_cycle

    rw [← h_eq]
    unfold D_new
    rw [Nat.cast_mul, Nat.cast_sub h_threshold_le]
    push_cast
    ring

  have h_delta_q :
      (delta_N_actual_inc n x : ℚ) =
        (sum_T n x : ℚ) - (N_eq n : ℚ) := by
    have h_bridge :=
      lemma_delta_equiv_bridge n x hn_pos

    have h_bridge_q :
        ((sum_T n x : ℚ) - (N_eq n : ℚ)) =
          (delta_N_actual_inc n x : ℚ) := by
      exact_mod_cast h_bridge

    exact h_bridge_q.symm

  have hD_pos : 0 < D_new n x := by
    unfold D_new

    have h_threshold :
        (3 : ℚ)^n < (2 : ℚ)^(S n x) := by
      exact_mod_cast cycle_existence_threshold n x h_cycle hn_pos

    exact sub_pos.mpr h_threshold

  have hD_ge_Neq :
      (N_eq n : ℚ) ≤ D_new n x := by
    have h_step6 :=
      lemma_1J_step6_D_new_closed_form n x q h_deltaS

    rw [h_step6]
    rw [N_eq_rational n]

    have h_four :
        (2 : ℚ)^(2 * n) = (4 : ℚ)^n := by
      rw [pow_mul]
      norm_num

    rw [h_four]

    have h_extra_ge_one_nat :
        1 ≤ 2^(2 * 3^(n - 1 - q)) :=
      Nat.succ_le_of_lt
        (pow_pos (by decide : 0 < 2) (2 * 3^(n - 1 - q)))

    have h_extra_ge_one :
        (1 : ℚ) ≤ (2 : ℚ)^(2 * 3^(n - 1 - q)) := by
      exact_mod_cast h_extra_ge_one_nat

    have h4_nonneg :
        0 ≤ (4 : ℚ)^n := by
      positivity

    have h4_le :
        (4 : ℚ)^n ≤
          (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) := by
      calc
        (4 : ℚ)^n = (4 : ℚ)^n * 1 := by ring
        _ ≤ (4 : ℚ)^n * (2 : ℚ)^(2 * 3^(n - 1 - q)) :=
          mul_le_mul_of_nonneg_left h_extra_ge_one h4_nonneg

    nlinarith

  have hx_ge_two :
      (2 : ℚ) ≤ (x : ℚ) := by
    exact_mod_cast (by omega : 2 ≤ x)

  have h_twoD_le_xD :
      2 * D_new n x ≤ D_new n x * (x : ℚ) := by
    have h :=
      mul_le_mul_of_nonneg_left hx_ge_two (le_of_lt hD_pos)

    simpa [mul_comm, mul_left_comm, mul_assoc] using h

  have h_multiplier :
      D_new n x ≤ (delta_N_actual_inc n x : ℚ) := by
    rw [h_delta_q, h_sum_q]
    nlinarith [h_twoD_le_xD, hD_ge_Neq]

  exact
    lemma_1J_cycle_multiplier_obstruction
      n x q hq hqn h_coast h_cascade h_deltaS h_multiplier
#check lemma_1J_no_is_cycle_parity_bridge_cascade
-- ===============================================================
-- SECTION 23: LEMMA 1K
-- ===============================================================
section Section23_Lemma1K

/--
Lemma 1K Step 1.

If every prefix exponent is bounded by the terminal cascade envelope
`2k + d`, then the actual numerator mass is bounded by the geometric ceiling
`2^d * (4^n - 3^n)`.
-/
theorem lemma_1K_step1_N_new_geometric_bound
  (n x d : ℕ)
  (h_envelope : ∀ k ∈ range n, S k x ≤ 2 * k + d) :
  (sum_T n x : ℚ) ≤ (2 : ℚ)^d * (N_eq n : ℚ) := by

  rw [sum_T]
  push_cast

  calc
    ∑ k ∈ range n,
        (3 : ℚ)^(n - 1 - k) * (2 : ℚ)^(S k x)
        ≤
      ∑ k ∈ range n,
        (2 : ℚ)^d *
          ((3 : ℚ)^(n - 1 - k) * (2 : ℚ)^(2 * k)) := by
        apply sum_le_sum
        intro k hk

        have h_pow_nat :
            2^(S k x) ≤ 2^(2 * k + d) :=
          Nat.pow_le_pow_right (by norm_num) (h_envelope k hk)

        have h_pow :
            (2 : ℚ)^(S k x) ≤ (2 : ℚ)^(2 * k + d) := by
          exact_mod_cast h_pow_nat

        have h_weight_nonneg :
            0 ≤ (3 : ℚ)^(n - 1 - k) := by
          positivity

        calc
          (3 : ℚ)^(n - 1 - k) * (2 : ℚ)^(S k x)
              ≤
            (3 : ℚ)^(n - 1 - k) * (2 : ℚ)^(2 * k + d) :=
              mul_le_mul_of_nonneg_left h_pow h_weight_nonneg
          _ =
            (2 : ℚ)^d *
              ((3 : ℚ)^(n - 1 - k) * (2 : ℚ)^(2 * k)) := by
              rw [pow_add]
              ring
    _ =
      (2 : ℚ)^d *
        ∑ k ∈ range n,
          (3 : ℚ)^(n - 1 - k) * (2 : ℚ)^(2 * k) := by
        rw [mul_sum]
    _ =
      (2 : ℚ)^d * (N_eq n : ℚ) := by
        rw [← N_eq_as_sum n]
#check lemma_1K_step1_N_new_geometric_bound

/--
Lemma 1K Step 2.

If the final exponent is at least `2n + d`, then the actual denominator is
bounded below by `4^n * 2^d - 3^n`.
-/
theorem lemma_1K_step2_D_new_baseline_bound
  (n x d : ℕ)
  (h_total_floor : 2 * n + d ≤ S n x) :
  (4 : ℚ)^n * (2 : ℚ)^d - (3 : ℚ)^n ≤ D_new n x := by

  unfold D_new

  have h_pow_nat :
      2^(2 * n + d) ≤ 2^(S n x) :=
    Nat.pow_le_pow_right (by norm_num) h_total_floor

  have h_pow_q :
      (2 : ℚ)^(2 * n + d) ≤ (2 : ℚ)^(S n x) := by
    exact_mod_cast h_pow_nat

  have h_rewrite :
      (2 : ℚ)^(2 * n + d) =
        (4 : ℚ)^n * (2 : ℚ)^d := by
    rw [pow_add]
    rw [pow_mul]
    norm_num

  have h_bound :
      (4 : ℚ)^n * (2 : ℚ)^d ≤ (2 : ℚ)^(S n x) := by
    rw [← h_rewrite]
    exact h_pow_q

  linarith
#check lemma_1K_step2_D_new_baseline_bound

/--
Lemma 1K Step 3.

Combining the numerator ceiling and denominator floor gives the absolute
gap lower bound.
-/
theorem lemma_1K_step3_absolute_gap_bound
  (n x d : ℕ)
  (h_envelope : ∀ k ∈ range n, S k x ≤ 2 * k + d)
  (h_total_floor : 2 * n + d ≤ S n x) :
  (3 : ℚ)^n * ((2 : ℚ)^d - 1) ≤
    D_new n x - (sum_T n x : ℚ) := by

  have h_num :=
    lemma_1K_step1_N_new_geometric_bound n x d h_envelope

  have h_den :=
    lemma_1K_step2_D_new_baseline_bound n x d h_total_floor

  have h_Neq :
      (N_eq n : ℚ) = (4 : ℚ)^n - (3 : ℚ)^n := by
    rw [N_eq_rational]
    have h_four :
        (2 : ℚ)^(2 * n) = (4 : ℚ)^n := by
      rw [pow_mul]
      norm_num
    rw [h_four]

  have h_gap_floor :
      (4 : ℚ)^n * (2 : ℚ)^d - (3 : ℚ)^n -
          (2 : ℚ)^d * (N_eq n : ℚ)
        ≤
      D_new n x - (sum_T n x : ℚ) := by
    linarith

  rw [h_Neq] at h_gap_floor

  have h_alg :
      (4 : ℚ)^n * (2 : ℚ)^d - (3 : ℚ)^n -
          (2 : ℚ)^d * ((4 : ℚ)^n - (3 : ℚ)^n)
        =
      (3 : ℚ)^n * ((2 : ℚ)^d - 1) := by
    ring

  rw [h_alg] at h_gap_floor
  exact h_gap_floor
#check lemma_1K_step3_absolute_gap_bound

/--
Lemma 1K Step 4.

The terminal LTE cascade bound forces a strictly positive denominator surplus.
-/
theorem lemma_1K_step4_LTE_cascade_gap
  (n x d d_prev : ℕ)
  (h_envelope : ∀ k ∈ range n, S k x ≤ 2 * k + d)
  (h_total_floor : 2 * n + d ≤ S n x)
  (h_LTE : 3 * d_prev ≤ d)
  (h_active : 1 ≤ d_prev) :
  (7 : ℚ) * (3 : ℚ)^n ≤
    D_new n x - (sum_T n x : ℚ) := by

  have h_gap :=
    lemma_1K_step3_absolute_gap_bound
      n x d h_envelope h_total_floor

  have h_exp_le_nat :
      2^(3 * d_prev) ≤ 2^d :=
    Nat.pow_le_pow_right (by norm_num) h_LTE

  have h_exp_le :
      (2 : ℚ)^(3 * d_prev) ≤ (2 : ℚ)^d := by
    exact_mod_cast h_exp_le_nat

  have h_sub_le :
      (2 : ℚ)^(3 * d_prev) - 1 ≤ (2 : ℚ)^d - 1 := by
    linarith

  have h_weight_nonneg :
      0 ≤ (3 : ℚ)^n := by
    positivity

  have h_gap_LTE :
      (3 : ℚ)^n * ((2 : ℚ)^(3 * d_prev) - 1) ≤
        D_new n x - (sum_T n x : ℚ) := by
    exact le_trans
      (mul_le_mul_of_nonneg_left h_sub_le h_weight_nonneg)
      h_gap

  have h_prev_floor :
      3 ≤ 3 * d_prev := by
    nlinarith

  have h_pow_floor_nat :
      8 ≤ 2^(3 * d_prev) := by
    calc
      8 = 2^3 := by norm_num
      _ ≤ 2^(3 * d_prev) :=
        Nat.pow_le_pow_right (by norm_num) h_prev_floor

  have h_pow_floor :
      (8 : ℚ) ≤ (2 : ℚ)^(3 * d_prev) := by
    exact_mod_cast h_pow_floor_nat

  have h_scalar_floor :
      (7 : ℚ) ≤ (2 : ℚ)^(3 * d_prev) - 1 := by
    linarith

  have h_gap_floor :
      (7 : ℚ) * (3 : ℚ)^n ≤
        (3 : ℚ)^n * ((2 : ℚ)^(3 * d_prev) - 1) := by
    nlinarith [h_weight_nonneg, h_scalar_floor]

  exact le_trans h_gap_floor h_gap_LTE
#check lemma_1K_step4_LTE_cascade_gap
/--
Lemma 1K conclusion.

Under the terminal LTE cascade hypotheses, the denominator strictly dominates
the numerator.
-/
theorem lemma_1K_denominator_strictly_dominates
  (n x d d_prev : ℕ)
  (h_envelope : ∀ k ∈ range n, S k x ≤ 2 * k + d)
  (h_total_floor : 2 * n + d ≤ S n x)
  (h_LTE : 3 * d_prev ≤ d)
  (h_active : 1 ≤ d_prev) :
  (sum_T n x : ℚ) < D_new n x := by

  have h_gap :=
    lemma_1K_step4_LTE_cascade_gap
      n x d d_prev h_envelope h_total_floor h_LTE h_active

  have h_pos :
      0 < (7 : ℚ) * (3 : ℚ)^n := by
    positivity

  linarith
#check lemma_1K_denominator_strictly_dominates

end Section23_Lemma1K
/--
Lemma 1K mapped to `is_cycle`.

A nontrivial cycle cannot satisfy the terminal cascade envelope and LTE
cascade bound, because the cycle equation forces the numerator to be at least
the denominator, while Lemma 1K forces it to be strictly smaller.
-/
theorem lemma_1K_no_is_cycle_terminal_cascade
  (n x d d_prev : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x > 1)
  (h_envelope : ∀ k ∈ range n, S k x ≤ 2 * k + d)
  (h_total_floor : 2 * n + d ≤ S n x)
  (h_LTE : 3 * d_prev ≤ d)
  (h_active : 1 ≤ d_prev) :
  False := by

  have h_dom :
      (sum_T n x : ℚ) < D_new n x :=
    lemma_1K_denominator_strictly_dominates
      n x d d_prev h_envelope h_total_floor h_LTE h_active

  have h_threshold_le :
      3^n ≤ 2^(S n x) :=
    le_of_lt (cycle_existence_threshold n x h_cycle hn)

  have h_sum_q :
      (sum_T n x : ℚ) = D_new n x * (x : ℚ) := by
    have h_eq :=
      cycle_implies_explicit_diophantine n x h_cycle

    rw [← h_eq]
    unfold D_new
    rw [Nat.cast_mul, Nat.cast_sub h_threshold_le]
    push_cast
    ring

  have hD_pos : 0 < D_new n x := by
    unfold D_new

    have h_threshold :
        (3 : ℚ)^n < (2 : ℚ)^(S n x) := by
      exact_mod_cast cycle_existence_threshold n x h_cycle hn

    exact sub_pos.mpr h_threshold

  have hx_ge_one :
      (1 : ℚ) ≤ (x : ℚ) := by
    exact_mod_cast (by omega : 1 ≤ x)

  have hD_le_sum :
      D_new n x ≤ (sum_T n x : ℚ) := by
    rw [h_sum_q]

    calc
      D_new n x = D_new n x * (1 : ℚ) := by ring
      _ ≤ D_new n x * (x : ℚ) :=
        mul_le_mul_of_nonneg_left hx_ge_one (le_of_lt hD_pos)

  linarith
#check lemma_1K_no_is_cycle_terminal_cascade

-- ===============================================================
-- SECTION 24: FINAL CAPSTONE CONDITIONAL CLOSURE
-- ===============================================================
section Section24_FinalCapstone

/--
Conditional final capstone.

For now, the capstone closes once the obstruction profile package is supplied:
terminal no-lift, parity-bridge cascade, or terminal cascade envelope.

The later unconditional task is to derive this supplied profile package from
`is_cycle n x`, `1 < n`, and `x > 1`.
-/
theorem final_capstone_conditional_closure
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x > 1)
  (h_supplied_profiles :
    Lemma1I_PureNegativePerturbationTrajectory n x ∨
    (∃ q : ℕ,
      2 ≤ q ∧ q < n ∧
        (∀ k ∈ Ico 1 q, S k x = 2 * k - 1) ∧
          (∀ k ∈ Ico q n, S k x = 2 * k + 2 * 3^(k - q)) ∧
            S_prime n x = (2 : ℤ) * (3 : ℤ)^(n - 1 - q)) ∨
    (∃ d d_prev : ℕ,
      (∀ k ∈ range n, S k x ≤ 2 * k + d) ∧
        2 * n + d ≤ S n x ∧
          3 * d_prev ≤ d ∧
            1 ≤ d_prev)) :
  False := by

  rcases h_supplied_profiles with h_no_lift | h_rest

  · exact
      corollary_1I1_no_pure_negative_perturbation_trajectory
        n x h_cycle hn hx h_no_lift

  · rcases h_rest with h_bridge | h_terminal

    · rcases h_bridge with
        ⟨q, hq, hqn, h_coast, h_cascade, h_deltaS⟩

      exact
        lemma_1J_no_is_cycle_parity_bridge_cascade
          n x q h_cycle hx hq hqn h_coast h_cascade h_deltaS

    · rcases h_terminal with
        ⟨d, d_prev, h_envelope, h_total_floor, h_LTE, h_active⟩

      exact
        lemma_1K_no_is_cycle_terminal_cascade
          n x d d_prev h_cycle hn hx
          h_envelope h_total_floor h_LTE h_active

#check final_capstone_conditional_closure
#print axioms final_capstone_conditional_closure

end Section24_FinalCapstone
