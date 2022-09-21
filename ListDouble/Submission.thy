theory Submission
  imports Defs
begin

fun double :: "'a list \<Rightarrow> 'a list"  where
  "double [] = []" |
  "double (x#xs) = x#x#(double xs)"

value "double [1,2,(3::nat)] = [1,1,2,2,3,3]"

theorem double_len: "length (double xs) = 2 * length xs"
  by (induction xs) simp+

lemma double_snoc:"double (snoc xs x) = snoc ( snoc (double xs) x) x"
  by (induction xs) auto

theorem reverse_double: "reverse (double xs) = double (reverse xs)"
  by (induction xs) (simp add: double_snoc)+

lemma double_add_tl:"(double xs) @ [a, a] = double (xs @ [a])"
  by (induction xs) simp+

theorem rev_double: "rev (double xs) = double (rev xs)"
  by (induction xs) (simp add: double_add_tl)+

end