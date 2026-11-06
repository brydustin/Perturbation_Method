theory DCX_nc_039
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0624: "dc_sub None 624"
  by (dc_eval dc_nc_0624)

lemma dc_nc_0625: "dc_sub None 625"
  by (dc_eval dc_nc_0625)

lemma dc_nc_0626: "dc_sub None 626"
  by (dc_eval dc_nc_0626)

lemma dc_nc_0627: "dc_sub None 627"
  by (dc_eval dc_nc_0627)

lemma dc_nc_0628: "dc_sub None 628"
  by (dc_eval dc_nc_0628)

lemma dc_nc_0629: "dc_sub None 629"
  by (dc_eval dc_nc_0629)

lemma dc_nc_0630: "dc_sub None 630"
  by (dc_eval dc_nc_0630)

lemma dc_nc_0631: "dc_sub None 631"
  by (dc_eval dc_nc_0631)

lemma dc_nc_0632: "dc_sub None 632"
  by (dc_eval dc_nc_0632)

lemma dc_nc_0633: "dc_sub None 633"
  by (dc_eval dc_nc_0633)

lemma dc_nc_0634: "dc_sub None 634"
  by (dc_eval dc_nc_0634)

lemma dc_nc_0635: "dc_sub None 635"
  by (dc_eval dc_nc_0635)

lemma dc_nc_0636: "dc_sub None 636"
  by (dc_eval dc_nc_0636)

lemma dc_nc_0637: "dc_sub None 637"
  by (dc_eval dc_nc_0637)

lemma dc_nc_0638: "dc_sub None 638"
  by (dc_eval dc_nc_0638)

lemma dc_nc_0639: "dc_sub None 639"
  by (dc_eval dc_nc_0639)

lemma upt_nc_039: "[624..<640] = [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]"
  by (simp add: upt_rec)

lemma sec_nc_039: "\<forall>j\<in>{16 * 39..<16 * 39 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 39..<16 * 39 + 16}"
  then have "j \<in> set [624..<640]" unfolding set_upt by simp
  then have "j \<in> set [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]" unfolding upt_nc_039 .
  then show "dc_sub None j" using dc_nc_0624 dc_nc_0625 dc_nc_0626 dc_nc_0627 dc_nc_0628 dc_nc_0629 dc_nc_0630 dc_nc_0631 dc_nc_0632 dc_nc_0633 dc_nc_0634 dc_nc_0635 dc_nc_0636 dc_nc_0637 dc_nc_0638 dc_nc_0639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
