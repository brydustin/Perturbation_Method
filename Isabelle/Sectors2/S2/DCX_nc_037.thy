theory DCX_nc_037
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0592: "dc_sub None 592"
  by (dc_eval dc_nc_0592)

lemma dc_nc_0593: "dc_sub None 593"
  by (dc_eval dc_nc_0593)

lemma dc_nc_0594: "dc_sub None 594"
  by (dc_eval dc_nc_0594)

lemma dc_nc_0595: "dc_sub None 595"
  by (dc_eval dc_nc_0595)

lemma dc_nc_0596: "dc_sub None 596"
  by (dc_eval dc_nc_0596)

lemma dc_nc_0597: "dc_sub None 597"
  by (dc_eval dc_nc_0597)

lemma dc_nc_0598: "dc_sub None 598"
  by (dc_eval dc_nc_0598)

lemma dc_nc_0599: "dc_sub None 599"
  by (dc_eval dc_nc_0599)

lemma dc_nc_0600: "dc_sub None 600"
  by (dc_eval dc_nc_0600)

lemma dc_nc_0601: "dc_sub None 601"
  by (dc_eval dc_nc_0601)

lemma dc_nc_0602: "dc_sub None 602"
  by (dc_eval dc_nc_0602)

lemma dc_nc_0603: "dc_sub None 603"
  by (dc_eval dc_nc_0603)

lemma dc_nc_0604: "dc_sub None 604"
  by (dc_eval dc_nc_0604)

lemma dc_nc_0605: "dc_sub None 605"
  by (dc_eval dc_nc_0605)

lemma dc_nc_0606: "dc_sub None 606"
  by (dc_eval dc_nc_0606)

lemma dc_nc_0607: "dc_sub None 607"
  by (dc_eval dc_nc_0607)

lemma upt_nc_037: "[592..<608] = [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]"
  by (simp add: upt_rec)

lemma sec_nc_037: "\<forall>j\<in>{16 * 37..<16 * 37 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 37..<16 * 37 + 16}"
  then have "j \<in> set [592..<608]" unfolding set_upt by simp
  then have "j \<in> set [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]" unfolding upt_nc_037 .
  then show "dc_sub None j" using dc_nc_0592 dc_nc_0593 dc_nc_0594 dc_nc_0595 dc_nc_0596 dc_nc_0597 dc_nc_0598 dc_nc_0599 dc_nc_0600 dc_nc_0601 dc_nc_0602 dc_nc_0603 dc_nc_0604 dc_nc_0605 dc_nc_0606 dc_nc_0607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
