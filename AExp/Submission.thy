theory Submission
  imports Defs
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 x = x" |
  "add (Suc n) x = 1 + add n x"

theorem add_assoc: "add (add x y) z = add x (add y z)"
  by (induction x) simp+

lemma add_0:"add x 0 = x"
  by (induction x) simp+

lemma add_plus:"add x y = add (x+y) 0"
  using add_0 by (induction x) simp+

theorem add_commut: "add x y = add y x"
  using add_plus add_0 by simp

datatype wexp = N val | V vname | Plus wexp wexp | Where wexp vname wexp

fun wval :: "wexp \<Rightarrow> state \<Rightarrow> val" where
  "wval (N n) s = n" |
  "wval (V x) s = s x" |
  "wval (Plus w1 w2) s = wval w1 s + wval w2 s" |
  "wval (Where w1 x w2) s = undefined"

fun inline :: "wexp \<Rightarrow> aexp" where
  "inline _ = undefined"

value
  "inline (Where (Plus (V ''x'') (V ''x'')) ''x'' (Plus (N 1) (N 1))) =
     aexp.Plus (aexp.Plus (aexp.N 1) (aexp.N 1)) (aexp.Plus (aexp.N 1) (aexp.N 1))"

theorem val_inline: "aval (inline e) s = wval e s"
  sorry

fun elim :: "wexp \<Rightarrow> wexp" where
  "elim _ = undefined"

theorem wval_elim: "wval (elim e) s = wval e s"
  sorry

end