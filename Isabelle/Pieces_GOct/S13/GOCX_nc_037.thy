theory GOCX_nc_037
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0592: "goc_sub None 592"
  by (goc_eval goc_nc_0592)

lemma goc_nc_0593: "goc_sub None 593"
  by (goc_eval goc_nc_0593)

lemma goc_nc_0594: "goc_sub None 594"
  by (goc_eval goc_nc_0594)

lemma goc_nc_0595: "goc_sub None 595"
  by (goc_eval goc_nc_0595)

lemma goc_nc_0596: "goc_sub None 596"
  by (goc_eval goc_nc_0596)

lemma goc_nc_0597: "goc_sub None 597"
  by (goc_eval goc_nc_0597)

lemma goc_nc_0598: "goc_sub None 598"
  by (goc_eval goc_nc_0598)

lemma goc_nc_0599: "goc_sub None 599"
  by (goc_eval goc_nc_0599)

lemma goc_nc_0600: "goc_sub None 600"
  by (goc_eval goc_nc_0600)

lemma goc_nc_0601: "goc_sub None 601"
  by (goc_eval goc_nc_0601)

lemma goc_nc_0602: "goc_sub None 602"
  by (goc_eval goc_nc_0602)

lemma goc_nc_0603: "goc_sub None 603"
  by (goc_eval goc_nc_0603)

lemma goc_nc_0604: "goc_sub None 604"
  by (goc_eval goc_nc_0604)

lemma goc_nc_0605: "goc_sub None 605"
  by (goc_eval goc_nc_0605)

lemma goc_nc_0606: "goc_sub None 606"
  by (goc_eval goc_nc_0606)

lemma goc_nc_0607: "goc_sub None 607"
  by (goc_eval goc_nc_0607)

lemma gupt_nc_037: "[592..<608] = [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]"
  by (simp add: upt_rec)

lemma gsec_nc_037: "\<forall>j\<in>{16 * 37..<16 * 37 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 37..<16 * 37 + 16}"
  then have "j \<in> set [592..<608]" unfolding set_upt by simp
  then have "j \<in> set [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]" unfolding gupt_nc_037 .
  then show "goc_sub None j" using goc_nc_0592 goc_nc_0593 goc_nc_0594 goc_nc_0595 goc_nc_0596 goc_nc_0597 goc_nc_0598 goc_nc_0599 goc_nc_0600 goc_nc_0601 goc_nc_0602 goc_nc_0603 goc_nc_0604 goc_nc_0605 goc_nc_0606 goc_nc_0607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
