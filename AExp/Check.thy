theory Check
  imports Submission
begin

theorem add_assoc: "add (add x y) z = add x (add y z)"
  by (rule Submission.add_assoc)

theorem add_commut: "add x y = add y x"
  by (rule Submission.add_commut)

theorem val_inline: "aval (inline e) s = wval e s"
  by (rule Submission.val_inline)

theorem wval_elim: "wval (elim e) s = wval e s"
  by (rule Submission.wval_elim)

end