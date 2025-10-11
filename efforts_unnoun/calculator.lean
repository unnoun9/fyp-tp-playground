-- the calculator will use these expressions as baseline for evaluating
-- calculator only available for natural numbers' addition, multiplication, and exponentiation, for now
-- the precedence order will be pow > mul > add, which is enforced in the some parsing function rather than evaluation
-- right now there is not parser here, just an evaluator that uses AST of expressions
inductive exp where
    | num : Nat → exp
    | add : exp → exp → exp
    | mul : exp → exp → exp
    | pow : exp → exp → exp

def add_op (a b : Nat) : Nat :=
    match b with
    | 0 => a
    | b' + 1 => Nat.succ (add_op a b')

def mul_op (a b : Nat) : Nat :=
    match b with
    | 0 => 0
    | b' + 1 => add_op (mul_op a b') a -- a + mul_op a b'

def pow_op (a b : Nat) : Nat :=
    match b with
    | 0 => 1
    | b' + 1 => mul_op (pow_op a b') a -- a * pow_op a b'

-- doing the following, since the built in Nat is correct in Lean:
-- proving that add_op is Nat.add so that I can safely use Nat.add in either the definitions of mul_op and pow_op or in the evaluation function
theorem add_op_eq_nat_add (a b : Nat) : add_op a b = a + b := by
    induction b with
    | zero => rw [add_op, Nat.add_zero]
    | succ b ih => rw [add_op, Nat.add_succ, ih]

-- simliar to add_op, proving that mul_op is Nat.mul so that I can safely use Nat.mul later
theorem mul_op_eq_nat_mul (a b : Nat) : mul_op a b = a * b := by
    induction b with
    | zero => rw [mul_op, Nat.mul_zero]
    | succ b ih => rw [mul_op, ih, add_op_eq_nat_add, Nat.mul_succ]

-- and similarly, doing the same for pow
theorem pow_op_eq_nat_pow (a b : Nat) : pow_op a b = a ^ b := by
    induction b with
    | zero => rw [pow_op, Nat.pow_zero]
    | succ b ih => rw [pow_op, ih, mul_op_eq_nat_mul, Nat.pow_succ]

def eval (expression : exp) : Nat :=
    match expression with
    | exp.num const => const
    | exp.add e1 e2 => (eval e1) + (eval e2) -- add_op (eval e1) (eval e2)
    | exp.mul e1 e2 => (eval e1) * (eval e2) -- mul_op (eval e1) (eval e2)
    | exp.pow e1 e2 => (eval e1) ^ (eval e2) -- pow_op (eval e1) (eval e2)

#eval 52 + 27
#eval eval (exp.add (exp.num 27) (exp.num 52))
#eval 2^10 + 2 * 2 * 2^8
#eval eval (exp.add (exp.pow (exp.num 2) (exp.num 10)) (exp.mul (exp.num 2) (exp.mul (exp.num 2) (exp.pow (exp.num 2) (exp.num 8)))))

-- proving addition laws:
theorem eval_add_assoc (a b c : Nat) : eval (exp.add (exp.add (exp.num a) (exp.num b)) (exp.num c)) = eval (exp.add (exp.num a) (exp.add (exp.num b) (exp.num c))) := by
    repeat rw [eval]
    rw [Nat.add_assoc]

theorem eval_add_id (a : Nat) : eval (exp.add (exp.num a) (exp.num 0)) = eval (exp.num a) := by
    repeat rw [eval]
    rw [Nat.add_zero]

theorem eval_add_comm (a b: Nat) : eval (exp.add (exp.num a) (exp.num b)) = eval (exp.add (exp.num b) (exp.num a))  := by
    repeat rw [eval]
    rw [Nat.add_comm]

-- proving multiplication laws:
theorem eval_mul_assoc (a b c : Nat) : eval (exp.mul (exp.mul (exp.num a) (exp.num b)) (exp.num c)) = eval (exp.mul (exp.num a) (exp.mul (exp.num b) (exp.num c))) := by
    repeat rw [eval]
    rw [Nat.mul_assoc]

theorem eval_mul_id (a : Nat) : eval (exp.mul (exp.num a) (exp.num 1)) = eval (exp.num a) := by
    repeat rw [eval]
    rw [Nat.mul_one]

theorem eval_mul_comm (a b: Nat) : eval (exp.mul (exp.num a) (exp.num b)) = eval (exp.mul (exp.num b) (exp.num a))  := by
    repeat rw [eval]
    rw [Nat.mul_comm]

theorem eval_two_mul (a : Nat) : eval (exp.mul (exp.num 2) (exp.num a)) = eval (exp.add (exp.num a) (exp.num a)) := by
    repeat rw [eval]
    rw [Nat.two_mul]

-- distributive laws:
theorem eval_left_distrib (a b c : Nat) : eval (exp.mul (exp.num a) (exp.add (exp.num b) (exp.num c))) = eval (exp.add (exp.mul (exp.num a) (exp.num b)) (exp.mul (exp.num a) (exp.num c))) := by
    repeat rw [eval]
    rw [Nat.left_distrib]

theorem eval_right_distrib (a b c : Nat) : eval (exp.mul (exp.add (exp.num a) (exp.num b)) (exp.num c)) = eval (exp.add (exp.mul (exp.num a) (exp.num c)) (exp.mul (exp.num b) (exp.num c))):= by
    repeat rw [eval]
    rw [Nat.right_distrib]

-- proving power laws:
theorem eval_pow_one (a : Nat) : eval (exp.pow (exp.num a) (exp.num 1)) = eval (exp.num a) := by
    repeat rw [eval]
    rw [Nat.pow_one]

theorem eval_pow_zero (a : Nat) : eval (exp.pow (exp.num a) (exp.num 0)) = eval (exp.num 1) := by
    repeat rw [eval]
    rw [Nat.pow_zero]

theorem eval_zero_pow_zero : eval (exp.pow (exp.num 0) (exp.num 0)) = eval (exp.num 1) := by
    repeat rw [eval]

theorem eval_zero_pow (a : Nat) (h: a > 0): eval (exp.pow (exp.num 0) (exp.num a)) = eval (exp.num 0) := by
    repeat rw [eval]
    exact Nat.zero_pow h

theorem eval_one_pow (a : Nat) : eval (exp.pow (exp.num 1) (exp.num a)) = eval (exp.num 1) := by
    repeat rw [eval]
    rw [Nat.one_pow]

theorem eval_pow_two (a : Nat) : eval (exp.pow (exp.num a) (exp.num 2)) = eval (exp.mul (exp.num a) (exp.num a)) := by
    repeat rw [eval]
    rw [Nat.pow_two]

theorem eval_pow_add (a m n : Nat) : eval (exp.pow (exp.num a) (exp.add (exp.num m) (exp.num n))) = eval (exp.mul (exp.pow (exp.num a) (exp.num m)) (exp.pow (exp.num a) (exp.num n))) := by
    repeat rw [eval]
    rw [Nat.pow_add]

theorem eval_mul_pow (a b n : Nat) : eval (exp.pow (exp.mul (exp.num a) (exp.num b)) (exp.num n)) = eval (exp.mul (exp.pow (exp.num a) (exp.num n)) (exp.pow (exp.num b) (exp.num n))) := by
    repeat rw [eval]
    rw [Nat.mul_pow]

theorem eval_pow_pow (a m n : Nat) : eval (exp.pow (exp.pow (exp.num a) (exp.num m)) (exp.num n)) = eval (exp.pow (exp.num a) (exp.mul (exp.num m) (exp.num n))) := by
    repeat rw [eval]
    induction n with
    | zero => rw [Nat.pow_zero, Nat.mul_zero, Nat.pow_zero]
    | succ l h => rw [Nat.pow_succ, h, Nat.mul_succ, Nat.pow_add]

-- not sure if this is enough to "formally verify" a calculator here in lean...
