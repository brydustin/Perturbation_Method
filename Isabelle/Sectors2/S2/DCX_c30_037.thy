theory DCX_c30_037
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0592: "dc_sub dc_b30 592"
  by (dc_eval dc_c30_0592)

lemma dc_c30_0593: "dc_sub dc_b30 593"
  by (dc_eval dc_c30_0593)

lemma dc_c30_0594: "dc_sub dc_b30 594"
  by (dc_eval dc_c30_0594)

lemma dc_c30_0595: "dc_sub dc_b30 595"
  by (dc_eval dc_c30_0595)

lemma dc_c30_0596: "dc_sub dc_b30 596"
  by (dc_eval dc_c30_0596)

lemma dc_c30_0597: "dc_sub dc_b30 597"
  by (dc_eval dc_c30_0597)

lemma dc_c30_0598: "dc_sub dc_b30 598"
  by (dc_eval dc_c30_0598)

lemma dc_c30_0599: "dc_sub dc_b30 599"
  by (dc_eval dc_c30_0599)

lemma dc_c30_0600: "dc_sub dc_b30 600"
  by (dc_eval dc_c30_0600)

lemma dc_c30_0601: "dc_sub dc_b30 601"
  by (dc_eval dc_c30_0601)

lemma dc_c30_0602: "dc_sub dc_b30 602"
  by (dc_eval dc_c30_0602)

lemma dc_c30_0603: "dc_sub dc_b30 603"
  by (dc_eval dc_c30_0603)

lemma dc_c30_0604: "dc_sub dc_b30 604"
  by (dc_eval dc_c30_0604)

lemma dc_c30_0605: "dc_sub dc_b30 605"
  by (dc_eval dc_c30_0605)

lemma dc_c30_0606: "dc_sub dc_b30 606"
  by (dc_eval dc_c30_0606)

lemma dc_c30_0607: "dc_sub dc_b30 607"
  by (dc_eval dc_c30_0607)

lemma upt_c30_037: "[592..<608] = [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]"
  by (simp add: upt_rec)

lemma sec_c30_037: "\<forall>j\<in>{16 * 37..<16 * 37 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 37..<16 * 37 + 16}"
  then have "j \<in> set [592..<608]" unfolding set_upt by simp
  then have "j \<in> set [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]" unfolding upt_c30_037 .
  then show "dc_sub dc_b30 j" using dc_c30_0592 dc_c30_0593 dc_c30_0594 dc_c30_0595 dc_c30_0596 dc_c30_0597 dc_c30_0598 dc_c30_0599 dc_c30_0600 dc_c30_0601 dc_c30_0602 dc_c30_0603 dc_c30_0604 dc_c30_0605 dc_c30_0606 dc_c30_0607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
