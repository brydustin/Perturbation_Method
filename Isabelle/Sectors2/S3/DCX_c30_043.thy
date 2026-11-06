theory DCX_c30_043
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0688: "dc_sub dc_b30 688"
  by (dc_eval dc_c30_0688)

lemma dc_c30_0689: "dc_sub dc_b30 689"
  by (dc_eval dc_c30_0689)

lemma dc_c30_0690: "dc_sub dc_b30 690"
  by (dc_eval dc_c30_0690)

lemma dc_c30_0691: "dc_sub dc_b30 691"
  by (dc_eval dc_c30_0691)

lemma dc_c30_0692: "dc_sub dc_b30 692"
  by (dc_eval dc_c30_0692)

lemma dc_c30_0693: "dc_sub dc_b30 693"
  by (dc_eval dc_c30_0693)

lemma dc_c30_0694: "dc_sub dc_b30 694"
  by (dc_eval dc_c30_0694)

lemma dc_c30_0695: "dc_sub dc_b30 695"
  by (dc_eval dc_c30_0695)

lemma dc_c30_0696: "dc_sub dc_b30 696"
  by (dc_eval dc_c30_0696)

lemma dc_c30_0697: "dc_sub dc_b30 697"
  by (dc_eval dc_c30_0697)

lemma dc_c30_0698: "dc_sub dc_b30 698"
  by (dc_eval dc_c30_0698)

lemma dc_c30_0699: "dc_sub dc_b30 699"
  by (dc_eval dc_c30_0699)

lemma dc_c30_0700: "dc_sub dc_b30 700"
  by (dc_eval dc_c30_0700)

lemma dc_c30_0701: "dc_sub dc_b30 701"
  by (dc_eval dc_c30_0701)

lemma dc_c30_0702: "dc_sub dc_b30 702"
  by (dc_eval dc_c30_0702)

lemma dc_c30_0703: "dc_sub dc_b30 703"
  by (dc_eval dc_c30_0703)

lemma upt_c30_043: "[688..<704] = [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]"
  by (simp add: upt_rec)

lemma sec_c30_043: "\<forall>j\<in>{16 * 43..<16 * 43 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 43..<16 * 43 + 16}"
  then have "j \<in> set [688..<704]" unfolding set_upt by simp
  then have "j \<in> set [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]" unfolding upt_c30_043 .
  then show "dc_sub dc_b30 j" using dc_c30_0688 dc_c30_0689 dc_c30_0690 dc_c30_0691 dc_c30_0692 dc_c30_0693 dc_c30_0694 dc_c30_0695 dc_c30_0696 dc_c30_0697 dc_c30_0698 dc_c30_0699 dc_c30_0700 dc_c30_0701 dc_c30_0702 dc_c30_0703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
