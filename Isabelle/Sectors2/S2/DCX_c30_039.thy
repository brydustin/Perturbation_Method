theory DCX_c30_039
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0624: "dc_sub dc_b30 624"
  by (dc_eval dc_c30_0624)

lemma dc_c30_0625: "dc_sub dc_b30 625"
  by (dc_eval dc_c30_0625)

lemma dc_c30_0626: "dc_sub dc_b30 626"
  by (dc_eval dc_c30_0626)

lemma dc_c30_0627: "dc_sub dc_b30 627"
  by (dc_eval dc_c30_0627)

lemma dc_c30_0628: "dc_sub dc_b30 628"
  by (dc_eval dc_c30_0628)

lemma dc_c30_0629: "dc_sub dc_b30 629"
  by (dc_eval dc_c30_0629)

lemma dc_c30_0630: "dc_sub dc_b30 630"
  by (dc_eval dc_c30_0630)

lemma dc_c30_0631: "dc_sub dc_b30 631"
  by (dc_eval dc_c30_0631)

lemma dc_c30_0632: "dc_sub dc_b30 632"
  by (dc_eval dc_c30_0632)

lemma dc_c30_0633: "dc_sub dc_b30 633"
  by (dc_eval dc_c30_0633)

lemma dc_c30_0634: "dc_sub dc_b30 634"
  by (dc_eval dc_c30_0634)

lemma dc_c30_0635: "dc_sub dc_b30 635"
  by (dc_eval dc_c30_0635)

lemma dc_c30_0636: "dc_sub dc_b30 636"
  by (dc_eval dc_c30_0636)

lemma dc_c30_0637: "dc_sub dc_b30 637"
  by (dc_eval dc_c30_0637)

lemma dc_c30_0638: "dc_sub dc_b30 638"
  by (dc_eval dc_c30_0638)

lemma dc_c30_0639: "dc_sub dc_b30 639"
  by (dc_eval dc_c30_0639)

lemma upt_c30_039: "[624..<640] = [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]"
  by (simp add: upt_rec)

lemma sec_c30_039: "\<forall>j\<in>{16 * 39..<16 * 39 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 39..<16 * 39 + 16}"
  then have "j \<in> set [624..<640]" unfolding set_upt by simp
  then have "j \<in> set [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]" unfolding upt_c30_039 .
  then show "dc_sub dc_b30 j" using dc_c30_0624 dc_c30_0625 dc_c30_0626 dc_c30_0627 dc_c30_0628 dc_c30_0629 dc_c30_0630 dc_c30_0631 dc_c30_0632 dc_c30_0633 dc_c30_0634 dc_c30_0635 dc_c30_0636 dc_c30_0637 dc_c30_0638 dc_c30_0639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
