theory GOCX_nc_039
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0624: "goc_sub None 624"
  by (goc_eval goc_nc_0624)

lemma goc_nc_0625: "goc_sub None 625"
  by (goc_eval goc_nc_0625)

lemma goc_nc_0626: "goc_sub None 626"
  by (goc_eval goc_nc_0626)

lemma goc_nc_0627: "goc_sub None 627"
  by (goc_eval goc_nc_0627)

lemma goc_nc_0628: "goc_sub None 628"
  by (goc_eval goc_nc_0628)

lemma goc_nc_0629: "goc_sub None 629"
  by (goc_eval goc_nc_0629)

lemma goc_nc_0630: "goc_sub None 630"
  by (goc_eval goc_nc_0630)

lemma goc_nc_0631: "goc_sub None 631"
  by (goc_eval goc_nc_0631)

lemma goc_nc_0632: "goc_sub None 632"
  by (goc_eval goc_nc_0632)

lemma goc_nc_0633: "goc_sub None 633"
  by (goc_eval goc_nc_0633)

lemma goc_nc_0634: "goc_sub None 634"
  by (goc_eval goc_nc_0634)

lemma goc_nc_0635: "goc_sub None 635"
  by (goc_eval goc_nc_0635)

lemma goc_nc_0636: "goc_sub None 636"
  by (goc_eval goc_nc_0636)

lemma goc_nc_0637: "goc_sub None 637"
  by (goc_eval goc_nc_0637)

lemma goc_nc_0638: "goc_sub None 638"
  by (goc_eval goc_nc_0638)

lemma goc_nc_0639: "goc_sub None 639"
  by (goc_eval goc_nc_0639)

lemma gupt_nc_039: "[624..<640] = [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]"
  by (simp add: upt_rec)

lemma gsec_nc_039: "\<forall>j\<in>{16 * 39..<16 * 39 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 39..<16 * 39 + 16}"
  then have "j \<in> set [624..<640]" unfolding set_upt by simp
  then have "j \<in> set [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]" unfolding gupt_nc_039 .
  then show "goc_sub None j" using goc_nc_0624 goc_nc_0625 goc_nc_0626 goc_nc_0627 goc_nc_0628 goc_nc_0629 goc_nc_0630 goc_nc_0631 goc_nc_0632 goc_nc_0633 goc_nc_0634 goc_nc_0635 goc_nc_0636 goc_nc_0637 goc_nc_0638 goc_nc_0639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
