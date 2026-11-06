theory OCX_nc_039
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0624: "oc_sub None 624"
  by (oc_eval oc_nc_0624)

lemma oc_nc_0625: "oc_sub None 625"
  by (oc_eval oc_nc_0625)

lemma oc_nc_0626: "oc_sub None 626"
  by (oc_eval oc_nc_0626)

lemma oc_nc_0627: "oc_sub None 627"
  by (oc_eval oc_nc_0627)

lemma oc_nc_0628: "oc_sub None 628"
  by (oc_eval oc_nc_0628)

lemma oc_nc_0629: "oc_sub None 629"
  by (oc_eval oc_nc_0629)

lemma oc_nc_0630: "oc_sub None 630"
  by (oc_eval oc_nc_0630)

lemma oc_nc_0631: "oc_sub None 631"
  by (oc_eval oc_nc_0631)

lemma oc_nc_0632: "oc_sub None 632"
  by (oc_eval oc_nc_0632)

lemma oc_nc_0633: "oc_sub None 633"
  by (oc_eval oc_nc_0633)

lemma oc_nc_0634: "oc_sub None 634"
  by (oc_eval oc_nc_0634)

lemma oc_nc_0635: "oc_sub None 635"
  by (oc_eval oc_nc_0635)

lemma oc_nc_0636: "oc_sub None 636"
  by (oc_eval oc_nc_0636)

lemma oc_nc_0637: "oc_sub None 637"
  by (oc_eval oc_nc_0637)

lemma oc_nc_0638: "oc_sub None 638"
  by (oc_eval oc_nc_0638)

lemma oc_nc_0639: "oc_sub None 639"
  by (oc_eval oc_nc_0639)

lemma upt_nc_039: "[624..<640] = [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]"
  by (simp add: upt_rec)

lemma sec_nc_039: "\<forall>j\<in>{16 * 39..<16 * 39 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 39..<16 * 39 + 16}"
  then have "j \<in> set [624..<640]" unfolding set_upt by simp
  then have "j \<in> set [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]" unfolding upt_nc_039 .
  then show "oc_sub None j" using oc_nc_0624 oc_nc_0625 oc_nc_0626 oc_nc_0627 oc_nc_0628 oc_nc_0629 oc_nc_0630 oc_nc_0631 oc_nc_0632 oc_nc_0633 oc_nc_0634 oc_nc_0635 oc_nc_0636 oc_nc_0637 oc_nc_0638 oc_nc_0639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
