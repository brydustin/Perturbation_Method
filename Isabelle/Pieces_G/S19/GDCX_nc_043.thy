theory GDCX_nc_043
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0688: "gdc_sub None 688"
  by (gdc_eval gdc_nc_0688)

lemma gdc_nc_0689: "gdc_sub None 689"
  by (gdc_eval gdc_nc_0689)

lemma gdc_nc_0690: "gdc_sub None 690"
  by (gdc_eval gdc_nc_0690)

lemma gdc_nc_0691: "gdc_sub None 691"
  by (gdc_eval gdc_nc_0691)

lemma gdc_nc_0692: "gdc_sub None 692"
  by (gdc_eval gdc_nc_0692)

lemma gdc_nc_0693: "gdc_sub None 693"
  by (gdc_eval gdc_nc_0693)

lemma gdc_nc_0694: "gdc_sub None 694"
  by (gdc_eval gdc_nc_0694)

lemma gdc_nc_0695: "gdc_sub None 695"
  by (gdc_eval gdc_nc_0695)

lemma gdc_nc_0696: "gdc_sub None 696"
  by (gdc_eval gdc_nc_0696)

lemma gdc_nc_0697: "gdc_sub None 697"
  by (gdc_eval gdc_nc_0697)

lemma gdc_nc_0698: "gdc_sub None 698"
  by (gdc_eval gdc_nc_0698)

lemma gdc_nc_0699: "gdc_sub None 699"
  by (gdc_eval gdc_nc_0699)

lemma gdc_nc_0700: "gdc_sub None 700"
  by (gdc_eval gdc_nc_0700)

lemma gdc_nc_0701: "gdc_sub None 701"
  by (gdc_eval gdc_nc_0701)

lemma gdc_nc_0702: "gdc_sub None 702"
  by (gdc_eval gdc_nc_0702)

lemma gdc_nc_0703: "gdc_sub None 703"
  by (gdc_eval gdc_nc_0703)

lemma gupt_nc_043: "[688..<704] = [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]"
  by (simp add: upt_rec)

lemma gsec_nc_043: "\<forall>j\<in>{16 * 43..<16 * 43 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 43..<16 * 43 + 16}"
  then have "j \<in> set [688..<704]" unfolding set_upt by simp
  then have "j \<in> set [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]" unfolding gupt_nc_043 .
  then show "gdc_sub None j" using gdc_nc_0688 gdc_nc_0689 gdc_nc_0690 gdc_nc_0691 gdc_nc_0692 gdc_nc_0693 gdc_nc_0694 gdc_nc_0695 gdc_nc_0696 gdc_nc_0697 gdc_nc_0698 gdc_nc_0699 gdc_nc_0700 gdc_nc_0701 gdc_nc_0702 gdc_nc_0703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
