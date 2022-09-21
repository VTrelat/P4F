theory Check
  imports Submission
begin

theorem double_len: "length (double xs) = 2 * length xs"
  by (rule Submission.double_len)

theorem reverse_double: "reverse (double xs) = double (reverse xs)"
  by (rule Submission.reverse_double)

theorem rev_double: "rev (double xs) = double (rev xs)"
  by (rule Submission.rev_double)

end