
set_option pp.parens true

example (n m:Nat) :  (m + n) + 1 = m + (n + 1) := by
  rfl -- this is one of the definitions of addition

example (n : Nat) : n + 0 = n := by
  rfl -- this is one of the definitions of addition

theorem zpnen (n: Nat) :  0 + n = n + 0 := by
  induction n with
    | zero => rfl
    | succ n hyp => calc
      0 + (n + 1) = (0 + n) + 1 := by rfl
                  _ = (n + 0) + 1 := by rw [hyp]
                  _ = n + 1 := by rfl

theorem spmn (n m:Nat) : (m + n) + 1 = (m + 1) + n := by
  induction n with
    | zero => rfl
    | succ n ih => calc
      (m + (n + 1)) + 1 = ((m + n) + 1) + 1 := by rfl
                      _ = ((m + 1) + n) + 1 := by rw [ih]
                      _ = (m + 1) + (n + 1) := by rfl

theorem comm (n m:Nat) : n + m = m + n := by
  induction n with
    | zero => rw [zpnen]
    | succ n ih => calc
      (n + 1) + m = (n + m) + 1 := by rw [spmn]
                  _ = (m + n) + 1 := by rw [ih]
                  _ = m + (n + 1) := by rfl
