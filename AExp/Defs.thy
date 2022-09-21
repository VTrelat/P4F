theory Defs
  imports "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

fun deduplicate :: "'a list \<Rightarrow> 'a list" where
  "deduplicate [] = []"
| "deduplicate [x] = [x]"
| "deduplicate (x # y # xs) = (if x = y then deduplicate (y # xs) else x # deduplicate (y # xs))"

lemma "length (deduplicate xs) \<le> length xs"
  by (induction xs rule: deduplicate.induct) auto

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a' (N n) = N n"
| "subst x a' (V y) = (if x=y then a' else V y)"
| "subst x a' (Plus a1 a2) = Plus (subst x a' a1) (subst x a' a2)"

lemma subst_lemma: "aval (subst x a' a) s = aval a (s(x:=aval a' s))"
  by (induct a) auto

lemma comp: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
  by (simp add: subst_lemma)

datatype aexp' = N' int | V' vname | PI' vname | Plus' aexp' aexp'

fun aval' where
  "aval' (N' n) s = (n,s)" |
  "aval' (V' x) s = (s x, s)" |
  "aval' (PI' x) s = (s x, s(x := 1 + s x))" |
  "aval' (Plus' a1 a2) s = (
    let (v1, s') = aval' a1 s; (v2, s'') = aval' a2 s'
    in (v1 + v2, s''))"

lemma "aval' (Plus' (PI' x) (V' x)) <> \<noteq> aval' (Plus' (V' x) (PI' x)) <>"
  by auto

lemma aval'_inc': "aval' a s = (v,s') \<Longrightarrow> s x \<le> s' x"
  apply (induct a arbitrary: s s' v)
     apply (auto split: prod.splits)
  apply fastforce
  done

lemma aval'_inc:
  "aval' a <> = (v, s') \<Longrightarrow> 0 \<le> s' x"
  using aval'_inc' by (fastforce simp: null_state_def)

end