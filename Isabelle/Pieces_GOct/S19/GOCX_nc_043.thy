theory GOCX_nc_043
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0688: "goc_sub None 688"
  by (goc_eval goc_nc_0688)

lemma goc_nc_0689: "goc_sub None 689"
  by (goc_eval goc_nc_0689)

lemma goc_nc_0690: "goc_sub None 690"
  by (goc_eval goc_nc_0690)

lemma goc_nc_0691: "goc_sub None 691"
  by (goc_eval goc_nc_0691)

lemma goc_nc_0692: "goc_sub None 692"
  by (goc_eval goc_nc_0692)

lemma goc_nc_0693: "goc_sub None 693"
  by (goc_eval goc_nc_0693)

lemma goc_nc_0694: "goc_sub None 694"
  by (goc_eval goc_nc_0694)

lemma goc_nc_0695: "goc_sub None 695"
  by (goc_eval goc_nc_0695)

lemma goc_nc_0696: "goc_sub None 696"
  by (goc_eval goc_nc_0696)

lemma goc_nc_0697: "goc_sub None 697"
  by (goc_eval goc_nc_0697)

lemma goc_nc_0698: "goc_sub None 698"
  by (goc_eval goc_nc_0698)

lemma goc_nc_0699: "goc_sub None 699"
  by (goc_eval goc_nc_0699)

lemma goc_nc_0700: "goc_sub None 700"
  by (goc_eval goc_nc_0700)

lemma goc_nc_0701: "goc_sub None 701"
  by (goc_eval goc_nc_0701)

lemma goc_nc_0702: "goc_sub None 702"
  by (goc_eval goc_nc_0702)

lemma goc_nc_0703: "goc_sub None 703"
  by (goc_eval goc_nc_0703)

lemma gupt_nc_043: "[688..<704] = [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]"
  by (simp add: upt_rec)

lemma gsec_nc_043: "\<forall>j\<in>{16 * 43..<16 * 43 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 43..<16 * 43 + 16}"
  then have "j \<in> set [688..<704]" unfolding set_upt by simp
  then have "j \<in> set [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]" unfolding gupt_nc_043 .
  then show "goc_sub None j" using goc_nc_0688 goc_nc_0689 goc_nc_0690 goc_nc_0691 goc_nc_0692 goc_nc_0693 goc_nc_0694 goc_nc_0695 goc_nc_0696 goc_nc_0697 goc_nc_0698 goc_nc_0699 goc_nc_0700 goc_nc_0701 goc_nc_0702 goc_nc_0703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
