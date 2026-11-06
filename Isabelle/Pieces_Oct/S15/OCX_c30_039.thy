theory OCX_c30_039
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0624: "oc_sub oc_b30 624"
  by (oc_eval oc_c30_0624)

lemma oc_c30_0625: "oc_sub oc_b30 625"
  by (oc_eval oc_c30_0625)

lemma oc_c30_0626: "oc_sub oc_b30 626"
  by (oc_eval oc_c30_0626)

lemma oc_c30_0627: "oc_sub oc_b30 627"
  by (oc_eval oc_c30_0627)

lemma oc_c30_0628: "oc_sub oc_b30 628"
  by (oc_eval oc_c30_0628)

lemma oc_c30_0629: "oc_sub oc_b30 629"
  by (oc_eval oc_c30_0629)

lemma oc_c30_0630: "oc_sub oc_b30 630"
  by (oc_eval oc_c30_0630)

lemma oc_c30_0631: "oc_sub oc_b30 631"
  by (oc_eval oc_c30_0631)

lemma oc_c30_0632: "oc_sub oc_b30 632"
  by (oc_eval oc_c30_0632)

lemma oc_c30_0633: "oc_sub oc_b30 633"
  by (oc_eval oc_c30_0633)

lemma oc_c30_0634: "oc_sub oc_b30 634"
  by (oc_eval oc_c30_0634)

lemma oc_c30_0635: "oc_sub oc_b30 635"
  by (oc_eval oc_c30_0635)

lemma oc_c30_0636: "oc_sub oc_b30 636"
  by (oc_eval oc_c30_0636)

lemma oc_c30_0637: "oc_sub oc_b30 637"
  by (oc_eval oc_c30_0637)

lemma oc_c30_0638: "oc_sub oc_b30 638"
  by (oc_eval oc_c30_0638)

lemma oc_c30_0639: "oc_sub oc_b30 639"
  by (oc_eval oc_c30_0639)

lemma upt_c30_039: "[624..<640] = [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]"
  by (simp add: upt_rec)

lemma sec_c30_039: "\<forall>j\<in>{16 * 39..<16 * 39 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 39..<16 * 39 + 16}"
  then have "j \<in> set [624..<640]" unfolding set_upt by simp
  then have "j \<in> set [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]" unfolding upt_c30_039 .
  then show "oc_sub oc_b30 j" using oc_c30_0624 oc_c30_0625 oc_c30_0626 oc_c30_0627 oc_c30_0628 oc_c30_0629 oc_c30_0630 oc_c30_0631 oc_c30_0632 oc_c30_0633 oc_c30_0634 oc_c30_0635 oc_c30_0636 oc_c30_0637 oc_c30_0638 oc_c30_0639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
