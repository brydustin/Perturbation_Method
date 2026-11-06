theory GDCX_nc_037
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0592: "gdc_sub None 592"
  by (gdc_eval gdc_nc_0592)

lemma gdc_nc_0593: "gdc_sub None 593"
  by (gdc_eval gdc_nc_0593)

lemma gdc_nc_0594: "gdc_sub None 594"
  by (gdc_eval gdc_nc_0594)

lemma gdc_nc_0595: "gdc_sub None 595"
  by (gdc_eval gdc_nc_0595)

lemma gdc_nc_0596: "gdc_sub None 596"
  by (gdc_eval gdc_nc_0596)

lemma gdc_nc_0597: "gdc_sub None 597"
  by (gdc_eval gdc_nc_0597)

lemma gdc_nc_0598: "gdc_sub None 598"
  by (gdc_eval gdc_nc_0598)

lemma gdc_nc_0599: "gdc_sub None 599"
  by (gdc_eval gdc_nc_0599)

lemma gdc_nc_0600: "gdc_sub None 600"
  by (gdc_eval gdc_nc_0600)

lemma gdc_nc_0601: "gdc_sub None 601"
  by (gdc_eval gdc_nc_0601)

lemma gdc_nc_0602: "gdc_sub None 602"
  by (gdc_eval gdc_nc_0602)

lemma gdc_nc_0603: "gdc_sub None 603"
  by (gdc_eval gdc_nc_0603)

lemma gdc_nc_0604: "gdc_sub None 604"
  by (gdc_eval gdc_nc_0604)

lemma gdc_nc_0605: "gdc_sub None 605"
  by (gdc_eval gdc_nc_0605)

lemma gdc_nc_0606: "gdc_sub None 606"
  by (gdc_eval gdc_nc_0606)

lemma gdc_nc_0607: "gdc_sub None 607"
  by (gdc_eval gdc_nc_0607)

lemma gupt_nc_037: "[592..<608] = [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]"
  by (simp add: upt_rec)

lemma gsec_nc_037: "\<forall>j\<in>{16 * 37..<16 * 37 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 37..<16 * 37 + 16}"
  then have "j \<in> set [592..<608]" unfolding set_upt by simp
  then have "j \<in> set [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]" unfolding gupt_nc_037 .
  then show "gdc_sub None j" using gdc_nc_0592 gdc_nc_0593 gdc_nc_0594 gdc_nc_0595 gdc_nc_0596 gdc_nc_0597 gdc_nc_0598 gdc_nc_0599 gdc_nc_0600 gdc_nc_0601 gdc_nc_0602 gdc_nc_0603 gdc_nc_0604 gdc_nc_0605 gdc_nc_0606 gdc_nc_0607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
