theory OCX_nc_037
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0592: "oc_sub None 592"
  by (oc_eval oc_nc_0592)

lemma oc_nc_0593: "oc_sub None 593"
  by (oc_eval oc_nc_0593)

lemma oc_nc_0594: "oc_sub None 594"
  by (oc_eval oc_nc_0594)

lemma oc_nc_0595: "oc_sub None 595"
  by (oc_eval oc_nc_0595)

lemma oc_nc_0596: "oc_sub None 596"
  by (oc_eval oc_nc_0596)

lemma oc_nc_0597: "oc_sub None 597"
  by (oc_eval oc_nc_0597)

lemma oc_nc_0598: "oc_sub None 598"
  by (oc_eval oc_nc_0598)

lemma oc_nc_0599: "oc_sub None 599"
  by (oc_eval oc_nc_0599)

lemma oc_nc_0600: "oc_sub None 600"
  by (oc_eval oc_nc_0600)

lemma oc_nc_0601: "oc_sub None 601"
  by (oc_eval oc_nc_0601)

lemma oc_nc_0602: "oc_sub None 602"
  by (oc_eval oc_nc_0602)

lemma oc_nc_0603: "oc_sub None 603"
  by (oc_eval oc_nc_0603)

lemma oc_nc_0604: "oc_sub None 604"
  by (oc_eval oc_nc_0604)

lemma oc_nc_0605: "oc_sub None 605"
  by (oc_eval oc_nc_0605)

lemma oc_nc_0606: "oc_sub None 606"
  by (oc_eval oc_nc_0606)

lemma oc_nc_0607: "oc_sub None 607"
  by (oc_eval oc_nc_0607)

lemma upt_nc_037: "[592..<608] = [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]"
  by (simp add: upt_rec)

lemma sec_nc_037: "\<forall>j\<in>{16 * 37..<16 * 37 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 37..<16 * 37 + 16}"
  then have "j \<in> set [592..<608]" unfolding set_upt by simp
  then have "j \<in> set [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]" unfolding upt_nc_037 .
  then show "oc_sub None j" using oc_nc_0592 oc_nc_0593 oc_nc_0594 oc_nc_0595 oc_nc_0596 oc_nc_0597 oc_nc_0598 oc_nc_0599 oc_nc_0600 oc_nc_0601 oc_nc_0602 oc_nc_0603 oc_nc_0604 oc_nc_0605 oc_nc_0606 oc_nc_0607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
