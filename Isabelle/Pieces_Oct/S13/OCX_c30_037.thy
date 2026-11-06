theory OCX_c30_037
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0592: "oc_sub oc_b30 592"
  by (oc_eval oc_c30_0592)

lemma oc_c30_0593: "oc_sub oc_b30 593"
  by (oc_eval oc_c30_0593)

lemma oc_c30_0594: "oc_sub oc_b30 594"
  by (oc_eval oc_c30_0594)

lemma oc_c30_0595: "oc_sub oc_b30 595"
  by (oc_eval oc_c30_0595)

lemma oc_c30_0596: "oc_sub oc_b30 596"
  by (oc_eval oc_c30_0596)

lemma oc_c30_0597: "oc_sub oc_b30 597"
  by (oc_eval oc_c30_0597)

lemma oc_c30_0598: "oc_sub oc_b30 598"
  by (oc_eval oc_c30_0598)

lemma oc_c30_0599: "oc_sub oc_b30 599"
  by (oc_eval oc_c30_0599)

lemma oc_c30_0600: "oc_sub oc_b30 600"
  by (oc_eval oc_c30_0600)

lemma oc_c30_0601: "oc_sub oc_b30 601"
  by (oc_eval oc_c30_0601)

lemma oc_c30_0602: "oc_sub oc_b30 602"
  by (oc_eval oc_c30_0602)

lemma oc_c30_0603: "oc_sub oc_b30 603"
  by (oc_eval oc_c30_0603)

lemma oc_c30_0604: "oc_sub oc_b30 604"
  by (oc_eval oc_c30_0604)

lemma oc_c30_0605: "oc_sub oc_b30 605"
  by (oc_eval oc_c30_0605)

lemma oc_c30_0606: "oc_sub oc_b30 606"
  by (oc_eval oc_c30_0606)

lemma oc_c30_0607: "oc_sub oc_b30 607"
  by (oc_eval oc_c30_0607)

lemma upt_c30_037: "[592..<608] = [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]"
  by (simp add: upt_rec)

lemma sec_c30_037: "\<forall>j\<in>{16 * 37..<16 * 37 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 37..<16 * 37 + 16}"
  then have "j \<in> set [592..<608]" unfolding set_upt by simp
  then have "j \<in> set [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]" unfolding upt_c30_037 .
  then show "oc_sub oc_b30 j" using oc_c30_0592 oc_c30_0593 oc_c30_0594 oc_c30_0595 oc_c30_0596 oc_c30_0597 oc_c30_0598 oc_c30_0599 oc_c30_0600 oc_c30_0601 oc_c30_0602 oc_c30_0603 oc_c30_0604 oc_c30_0605 oc_c30_0606 oc_c30_0607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
