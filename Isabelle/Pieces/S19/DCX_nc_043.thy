theory DCX_nc_043
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0688: "dc_sub None 688"
  by (dc_eval dc_nc_0688)

lemma dc_nc_0689: "dc_sub None 689"
  by (dc_eval dc_nc_0689)

lemma dc_nc_0690: "dc_sub None 690"
  by (dc_eval dc_nc_0690)

lemma dc_nc_0691: "dc_sub None 691"
  by (dc_eval dc_nc_0691)

lemma dc_nc_0692: "dc_sub None 692"
  by (dc_eval dc_nc_0692)

lemma dc_nc_0693: "dc_sub None 693"
  by (dc_eval dc_nc_0693)

lemma dc_nc_0694: "dc_sub None 694"
  by (dc_eval dc_nc_0694)

lemma dc_nc_0695: "dc_sub None 695"
  by (dc_eval dc_nc_0695)

lemma dc_nc_0696: "dc_sub None 696"
  by (dc_eval dc_nc_0696)

lemma dc_nc_0697: "dc_sub None 697"
  by (dc_eval dc_nc_0697)

lemma dc_nc_0698: "dc_sub None 698"
  by (dc_eval dc_nc_0698)

lemma dc_nc_0699: "dc_sub None 699"
  by (dc_eval dc_nc_0699)

lemma dc_nc_0700: "dc_sub None 700"
  by (dc_eval dc_nc_0700)

lemma dc_nc_0701: "dc_sub None 701"
  by (dc_eval dc_nc_0701)

lemma dc_nc_0702: "dc_sub None 702"
  by (dc_eval dc_nc_0702)

lemma dc_nc_0703: "dc_sub None 703"
  by (dc_eval dc_nc_0703)

lemma upt_nc_043: "[688..<704] = [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]"
  by (simp add: upt_rec)

lemma sec_nc_043: "\<forall>j\<in>{16 * 43..<16 * 43 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 43..<16 * 43 + 16}"
  then have "j \<in> set [688..<704]" unfolding set_upt by simp
  then have "j \<in> set [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]" unfolding upt_nc_043 .
  then show "dc_sub None j" using dc_nc_0688 dc_nc_0689 dc_nc_0690 dc_nc_0691 dc_nc_0692 dc_nc_0693 dc_nc_0694 dc_nc_0695 dc_nc_0696 dc_nc_0697 dc_nc_0698 dc_nc_0699 dc_nc_0700 dc_nc_0701 dc_nc_0702 dc_nc_0703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
