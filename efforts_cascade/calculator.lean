-- calculator for natural numbers using custom operations for add, sub, mul, div

-- defining primitive operations
def add_op (a b : Nat) : Nat :=
  match b with
  | 0 => a
  | b' + 1 => Nat.succ (add_op a b')

def sub_op (a b : Nat) : Nat :=
  match b with
  | 0 => a
  | b' + 1 =>
    match a with
    | 0 => 0
    | a' + 1 => sub_op a' b'

def mul_op (a b : Nat) : Nat :=
  match b with
  | 0 => 0
  | b' + 1 => add_op a (mul_op a b')

def div_op (a b : Nat) : Nat :=
  if b = 0 then 0
  else if a < b then 0
  else Nat.succ (div_op (sub_op a b) b)
termination_by a
decreasing_by
  simp_wf; sorry  -- proof of termination omitted for now

-- quick checks
#eval add_op 5 3
#eval sub_op 10 4
#eval mul_op 4 6
#eval! div_op 15 3
#eval! div_op 7 0

-- proving addition lemmas
theorem add_op_zero (a : Nat) : add_op a 0 = a := by simp [add_op]

theorem zero_add_op (a : Nat) : add_op 0 a = a := by
  induction a with
  | zero => simp [add_op]
  | succ a ih => simp [add_op, ih]

theorem add_op_assoc (a b c : Nat) : add_op (add_op a b) c = add_op a (add_op b c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp [add_op, ih]

theorem add_op_comm (a b : Nat) : add_op a b = add_op b a := by
  induction b with
  | zero => simp [add_op, add_op_zero, zero_add_op]
  | succ b ih =>
    have h : add_op (b + 1) a = Nat.succ (add_op b a) := by
      induction a with
      | zero => simp [add_op, add_op_zero]
      | succ a ih' => simp [add_op, ih']
    simp [add_op, ih, h]

-- multiplication lemmas
theorem mul_op_zero (a : Nat) : mul_op a 0 = 0 := by simp [mul_op]

theorem zero_mul_op (a : Nat) : mul_op 0 a = 0 := by
  induction a with
  | zero => simp [mul_op]
  | succ a ih => simp [mul_op, ih, add_op_zero]

theorem mul_op_one (a : Nat) : mul_op a 1 = a := by simp [mul_op, add_op_zero]

theorem mul_op_assoc (a b c : Nat) : mul_op (mul_op a b) c = mul_op a (mul_op b c) := by
  induction c with
  | zero => simp [mul_op_zero]
  | succ c ih => simp [mul_op, ih, add_op_assoc]

theorem mul_op_comm (a b : Nat) : mul_op a b = mul_op b a := by
  induction b with
  | zero => simp [mul_op, mul_op_zero, zero_mul_op]
  | succ b ih =>
    calc
      mul_op a (b + 1)
        = add_op a (mul_op a b) := by simp [mul_op]
      _ = add_op a (mul_op b a) := by rw [ih]
      _ = add_op (mul_op b a) a := by rw [add_op_comm]
      _ = mul_op (b + 1) a     := by simp [mul_op]

-- distributivity
theorem left_distrib_op (a b c : Nat) :
    mul_op a (add_op b c) = add_op (mul_op a b) (mul_op a c) := by
  induction c with
  | zero => simp [add_op_zero, mul_op_zero]
  | succ c ih => simp [add_op, mul_op, ih, add_op_assoc, add_op_comm]

-- examples using our custom ops
#eval add_op (add_op 2 3) 4
#eval mul_op (mul_op 2 3) 4
#eval add_op 5 3
#eval mul_op 4 6
#eval mul_op 3 (add_op 2 4)

-- simple calculator frontend
def calculate (op : String) (x y : Nat) : Nat :=
  match op with
  | "plus" => add_op x y
  | "minus" => sub_op x y
  | "times" => mul_op x y
  | "divide" => div_op x y
  | _ => 0

#eval! calculate "plus" 12 8
#eval! calculate "times" 7 8
#eval! calculate "minus" 15 6
#eval! calculate "divide" 20 4
