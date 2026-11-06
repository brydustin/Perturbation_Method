theory OCX_c30_043
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0688: "oc_sub oc_b30 688"
  by (oc_eval oc_c30_0688)

lemma oc_c30_0689: "oc_sub oc_b30 689"
  by (oc_eval oc_c30_0689)

lemma oc_c30_0690: "oc_sub oc_b30 690"
  by (oc_eval oc_c30_0690)

lemma oc_c30_0691: "oc_sub oc_b30 691"
  by (oc_eval oc_c30_0691)

lemma oc_c30_0692: "oc_sub oc_b30 692"
  by (oc_eval oc_c30_0692)

lemma oc_c30_0693: "oc_sub oc_b30 693"
  by (oc_eval oc_c30_0693)

lemma oc_c30_0694: "oc_sub oc_b30 694"
  by (oc_eval oc_c30_0694)

lemma oc_c30_0695: "oc_sub oc_b30 695"
  by (oc_eval oc_c30_0695)

lemma oc_c30_0696: "oc_sub oc_b30 696"
  by (oc_eval oc_c30_0696)

lemma oc_c30_0697: "oc_sub oc_b30 697"
  by (oc_eval oc_c30_0697)

lemma oc_c30_0698: "oc_sub oc_b30 698"
  by (oc_eval oc_c30_0698)

lemma oc_c30_0699: "oc_sub oc_b30 699"
  by (oc_eval oc_c30_0699)

lemma oc_c30_0700: "oc_sub oc_b30 700"
  by (oc_eval oc_c30_0700)

lemma oc_c30_0701: "oc_sub oc_b30 701"
  by (oc_eval oc_c30_0701)

lemma oc_c30_0702: "oc_sub oc_b30 702"
  by (oc_eval oc_c30_0702)

lemma oc_c30_0703: "oc_sub oc_b30 703"
  by (oc_eval oc_c30_0703)

lemma upt_c30_043: "[688..<704] = [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]"
  by (simp add: upt_rec)

lemma sec_c30_043: "\<forall>j\<in>{16 * 43..<16 * 43 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 43..<16 * 43 + 16}"
  then have "j \<in> set [688..<704]" unfolding set_upt by simp
  then have "j \<in> set [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]" unfolding upt_c30_043 .
  then show "oc_sub oc_b30 j" using oc_c30_0688 oc_c30_0689 oc_c30_0690 oc_c30_0691 oc_c30_0692 oc_c30_0693 oc_c30_0694 oc_c30_0695 oc_c30_0696 oc_c30_0697 oc_c30_0698 oc_c30_0699 oc_c30_0700 oc_c30_0701 oc_c30_0702 oc_c30_0703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
