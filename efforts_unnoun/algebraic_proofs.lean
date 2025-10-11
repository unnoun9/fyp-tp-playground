-- All of these proofs worked with Lean4 v4.22 (probably also works with v4.23, but haven't confirmed)
--
-- Difference of squares: a^2 - b^2 = (a + b)(a - b)
--
theorem sq_sub_sq (a b : Nat) : a^2 - b^2 = (a + b) * (a - b) := by
    cases b with
    | zero => rw [Nat.add_zero, Nat.sub_zero, Nat.sub_zero, Nat.pow_two]
    | succ n =>
        symm
        rw [Nat.mul_sub, Nat.right_distrib, Nat.right_distrib, Nat.one_mul,
            ← Nat.pow_two, Nat.add_mul, ← Nat.pow_two, Nat.sub_add_eq,
            Nat.mul_succ, Nat.mul_comm a n, Nat.add_sub_cancel]

theorem sq_sub_sq' (a b : Int) : a^2 - b^2 = (a + b) * (a - b) := by
    rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm a b]
    rw [← Int.add_sub_assoc (a*a - b*a) (b*a) (b*b)]
    rw [Int.sub_add_cancel]
    repeat rw [Int.pow_succ]
    repeat rw [Int.pow_zero]
    repeat rw [Int.one_mul]

-- This is how to use an existing theorem
theorem sq_sub_sq_literal : 5^2 - 2^2 = (5 + 2) * (5 - 2) := sq_sub_sq 5 2

-- This is how to use an existing theorem in tactic mode using the `exact` tactic
theorem sq_sub_sq_literal' : 5^2 - 2^2 = (5 + 2) * (5 - 2) := by
    exact sq_sub_sq 5 2
--
-- Cube of sum: (a + b)^3 = a^3 + 3a^2b + 3ab^2 + b^3
--
-- Helper theorem
theorem pow_three (a : Nat) : a^3 = a * a * a := by
    repeat rw [Nat.pow_succ]
    rw [Nat.pow_zero, Nat.one_mul]

-- Helper theorem
theorem add_two_times_self_eq_three_times (a : Nat) : a + 2 * a = 3 * a := by
    rw [Nat.mul_comm 3 a, Nat.mul_succ, Nat.mul_comm, Nat.add_comm]

theorem add_pow_three (a b : Nat) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by
    rw [pow_three, Nat.add_mul, Nat.mul_add,
        Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.add_mul,
        Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul] -- Distribute addition over multiplication
    rw [← pow_three a, ← pow_three b] -- Get the `a^3` annd `b^3` terms
    rw [Nat.mul_right_comm a b a, Nat.mul_comm b a,
        Nat.mul_right_comm a b a ] -- Get the a^2b terms
    rw [Nat.mul_comm (b*b) a, ← Nat.mul_assoc a b b] -- Get the `a*b^2` terms
    -- Start adding like terms
    rw [Nat.add_assoc (a^3) (a*a*b) (a*a*b + a*b*b),
        ← Nat.add_assoc (a*a*b), ← Nat.two_mul (a*a*b)] -- Get `2*(a*a*b)` term
    rw [Nat.add_assoc (a*a*b) (a*b*b) (a*b*b + b^3),
        ← Nat.add_assoc (a*b*b) (a*b*b) (b^3), ← Nat.two_mul (a*b*b)] -- Get `2*(a*b*b)`term
    rw [Nat.add_assoc (a^3), ← Nat.add_assoc (a*a*b) (2*(a*b*b)) (b^3),
        ← Nat.add_assoc (2*(a*a*b) + a*b*b) (a*a*b + 2*(a*b*b)) (b^3),
        ← Nat.add_assoc (2 * (a * a * b) + a * b * b) (a*a*b) (2*(a*b*b)),
        Nat.add_comm (2*(a*a*b) + a*b*b) (a*a*b), ← Nat.add_assoc (a*a*b) (2*(a*a*b)) (a*b*b),
        add_two_times_self_eq_three_times, Nat.add_assoc (3*(a*a*b)) (a*b*b) (2*(a*b*b)),
        add_two_times_self_eq_three_times,
        ← Nat.pow_two, Nat.mul_assoc a b b, ← Nat.pow_two b,
        ← Nat.mul_assoc, ← Nat.mul_assoc] -- Shift a lot of brackets and do rearranges to get `3*a^2*b` and `3a*b^2` terms
    rw [← Nat.add_assoc, ← Nat.add_assoc] -- Shift the last set of brackets

--
-- Difference of cubes: a^3 - b^3 = (a - b)(a^2 + a*b + b^2)
--
theorem cube_sub_cube (a b : Int) : a^3 - b^3 = (a - b) * (a^2 + a*b + b^2) := by
    symm
    rw [Int.sub_mul]
    repeat rw [Int.mul_add]
    rw [Int.mul_comm a (a^2), Int.mul_comm b (b^2), ← Int.pow_succ, ← Int.pow_succ]
    simp only [Nat.reduceAdd]
    rw [← Int.mul_assoc, ← @Lean.Grind.Semiring.pow_two, ← Int.mul_left_comm, ← @Lean.Grind.Semiring.pow_two,
        Int.mul_comm b, Int.sub_eq_add_neg]
    repeat rw [Int.neg_add]
    repeat rw [Int.add_assoc]
    rw [Int.add_left_comm (a*b^2) (-(a^2*b)) (-(a*b^2) + -b^3),
        Int.add_neg_cancel_left, Int.add_neg_cancel_left, Int.add_neg_eq_sub]

--
-- Square of Trinomial: (a + b + c)^2 = a^2 + b^2 + c^2 + 2ab + 2bc + 2ca
--
theorem add_three_term_sq (a b c : Nat) : (a + b + c)^2 = a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*c*a := by
    rw [Nat.pow_two, Nat.add_mul, Nat.add_mul]
    repeat rw [Nat.mul_add]
    repeat rw [← Nat.pow_two]
    rw [Nat.mul_comm b a, Nat.mul_comm c b, Nat.mul_comm a c,
        Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
        Nat.add_left_comm (c*a) (a*b) (b^2 + (b*c + (c*a + (b*c + c^2)))),
        ← Nat.add_assoc (a*b) (a*b) (c * a + (b ^ 2 + (b * c + (c * a + (b * c + c ^ 2))))),
        ← Nat.two_mul, ← Nat.mul_assoc 2 a b,
        Nat.add_left_comm (b*c) (c*a) (b*c + c^2), ← Nat.add_assoc (b*c) (b*c) (c^2),
        ← Nat.two_mul, ← Nat.mul_assoc 2 b c,
        Nat.add_left_comm (c*a) (b^2) (c * a + (2 * b * c + c ^ 2)), ← Nat.add_assoc (c*a) (c*a) (2*b*c + c^2),
        ← Nat.two_mul, ← Nat.mul_assoc 2 c a,
        Nat.add_left_comm (2*c*a), Nat.add_comm (2*c*a),
        Nat.add_left_comm (2*b*c),
        Nat.add_left_comm (2*a*b), Nat.add_left_comm (2*a*b)]
    repeat rw [← Nat.add_assoc]
