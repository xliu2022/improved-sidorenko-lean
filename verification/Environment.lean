module

public import Lean

@[expose] public section

-- Query the official Lean runtime from within Lean. This does not rely on
-- version text printed by a command-line compatibility host.
#eval Lean.versionString
#eval Lean.githash

example : (1 : Nat) + 1 = 2 := by rfl
#print axioms Nat.add_comm
