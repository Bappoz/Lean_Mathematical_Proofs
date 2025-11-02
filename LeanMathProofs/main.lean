import LeanMathProofs.basics.basicOperators
open LeanMathProofs.basic

theorem id_theorem ( P: Prop) : P -> P  := by
  intro h
  exact h

theorem comm_and (P Q : Prop) : P ∧ Q -> Q ∧ P := by
  intro h
  cases h with
  | intro hp hq =>
    apply And.intro
    · exact hq
    · exact hp

#check comm_and


theorem double_neg (P : Prop) : P -> ¬¬P := by
  intro hp hnp
  apply hnp
  exact hp

#check double_neg



namespace Testing

theorem T (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
    a = b := h1
    b = c + 1 := h2
    c + 1 = d + 1 := congrArg Nat.succ h3
    d + 1 = 1 + d := Nat.add_comm d 1
    1 + d = e := Eq.symm h4

end Testing
#check Testing.T
