theory GDCX_nc_039
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0624: "gdc_sub None 624"
  by (gdc_eval gdc_nc_0624)

lemma gdc_nc_0625: "gdc_sub None 625"
  by (gdc_eval gdc_nc_0625)

lemma gdc_nc_0626: "gdc_sub None 626"
  by (gdc_eval gdc_nc_0626)

lemma gdc_nc_0627: "gdc_sub None 627"
  by (gdc_eval gdc_nc_0627)

lemma gdc_nc_0628: "gdc_sub None 628"
  by (gdc_eval gdc_nc_0628)

lemma gdc_nc_0629: "gdc_sub None 629"
  by (gdc_eval gdc_nc_0629)

lemma gdc_nc_0630: "gdc_sub None 630"
  by (gdc_eval gdc_nc_0630)

lemma gdc_nc_0631: "gdc_sub None 631"
  by (gdc_eval gdc_nc_0631)

lemma gdc_nc_0632: "gdc_sub None 632"
  by (gdc_eval gdc_nc_0632)

lemma gdc_nc_0633: "gdc_sub None 633"
  by (gdc_eval gdc_nc_0633)

lemma gdc_nc_0634: "gdc_sub None 634"
  by (gdc_eval gdc_nc_0634)

lemma gdc_nc_0635: "gdc_sub None 635"
  by (gdc_eval gdc_nc_0635)

lemma gdc_nc_0636: "gdc_sub None 636"
  by (gdc_eval gdc_nc_0636)

lemma gdc_nc_0637: "gdc_sub None 637"
  by (gdc_eval gdc_nc_0637)

lemma gdc_nc_0638: "gdc_sub None 638"
  by (gdc_eval gdc_nc_0638)

lemma gdc_nc_0639: "gdc_sub None 639"
  by (gdc_eval gdc_nc_0639)

lemma gupt_nc_039: "[624..<640] = [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]"
  by (simp add: upt_rec)

lemma gsec_nc_039: "\<forall>j\<in>{16 * 39..<16 * 39 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 39..<16 * 39 + 16}"
  then have "j \<in> set [624..<640]" unfolding set_upt by simp
  then have "j \<in> set [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]" unfolding gupt_nc_039 .
  then show "gdc_sub None j" using gdc_nc_0624 gdc_nc_0625 gdc_nc_0626 gdc_nc_0627 gdc_nc_0628 gdc_nc_0629 gdc_nc_0630 gdc_nc_0631 gdc_nc_0632 gdc_nc_0633 gdc_nc_0634 gdc_nc_0635 gdc_nc_0636 gdc_nc_0637 gdc_nc_0638 gdc_nc_0639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
