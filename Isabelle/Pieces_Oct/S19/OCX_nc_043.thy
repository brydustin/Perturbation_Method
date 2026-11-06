theory OCX_nc_043
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0688: "oc_sub None 688"
  by (oc_eval oc_nc_0688)

lemma oc_nc_0689: "oc_sub None 689"
  by (oc_eval oc_nc_0689)

lemma oc_nc_0690: "oc_sub None 690"
  by (oc_eval oc_nc_0690)

lemma oc_nc_0691: "oc_sub None 691"
  by (oc_eval oc_nc_0691)

lemma oc_nc_0692: "oc_sub None 692"
  by (oc_eval oc_nc_0692)

lemma oc_nc_0693: "oc_sub None 693"
  by (oc_eval oc_nc_0693)

lemma oc_nc_0694: "oc_sub None 694"
  by (oc_eval oc_nc_0694)

lemma oc_nc_0695: "oc_sub None 695"
  by (oc_eval oc_nc_0695)

lemma oc_nc_0696: "oc_sub None 696"
  by (oc_eval oc_nc_0696)

lemma oc_nc_0697: "oc_sub None 697"
  by (oc_eval oc_nc_0697)

lemma oc_nc_0698: "oc_sub None 698"
  by (oc_eval oc_nc_0698)

lemma oc_nc_0699: "oc_sub None 699"
  by (oc_eval oc_nc_0699)

lemma oc_nc_0700: "oc_sub None 700"
  by (oc_eval oc_nc_0700)

lemma oc_nc_0701: "oc_sub None 701"
  by (oc_eval oc_nc_0701)

lemma oc_nc_0702: "oc_sub None 702"
  by (oc_eval oc_nc_0702)

lemma oc_nc_0703: "oc_sub None 703"
  by (oc_eval oc_nc_0703)

lemma upt_nc_043: "[688..<704] = [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]"
  by (simp add: upt_rec)

lemma sec_nc_043: "\<forall>j\<in>{16 * 43..<16 * 43 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 43..<16 * 43 + 16}"
  then have "j \<in> set [688..<704]" unfolding set_upt by simp
  then have "j \<in> set [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]" unfolding upt_nc_043 .
  then show "oc_sub None j" using oc_nc_0688 oc_nc_0689 oc_nc_0690 oc_nc_0691 oc_nc_0692 oc_nc_0693 oc_nc_0694 oc_nc_0695 oc_nc_0696 oc_nc_0697 oc_nc_0698 oc_nc_0699 oc_nc_0700 oc_nc_0701 oc_nc_0702 oc_nc_0703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
