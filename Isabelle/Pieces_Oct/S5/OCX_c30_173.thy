theory OCX_c30_173
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2768: "oc_sub oc_b30 2768"
  by (oc_eval oc_c30_2768)

lemma oc_c30_2769: "oc_sub oc_b30 2769"
  by (oc_eval oc_c30_2769)

lemma oc_c30_2770: "oc_sub oc_b30 2770"
  by (oc_eval oc_c30_2770)

lemma oc_c30_2771: "oc_sub oc_b30 2771"
  by (oc_eval oc_c30_2771)

lemma oc_c30_2772: "oc_sub oc_b30 2772"
  by (oc_eval oc_c30_2772)

lemma oc_c30_2773: "oc_sub oc_b30 2773"
  by (oc_eval oc_c30_2773)

lemma oc_c30_2774: "oc_sub oc_b30 2774"
  by (oc_eval oc_c30_2774)

lemma oc_c30_2775: "oc_sub oc_b30 2775"
  by (oc_eval oc_c30_2775)

lemma oc_c30_2776: "oc_sub oc_b30 2776"
  by (oc_eval oc_c30_2776)

lemma oc_c30_2777: "oc_sub oc_b30 2777"
  by (oc_eval oc_c30_2777)

lemma oc_c30_2778: "oc_sub oc_b30 2778"
  by (oc_eval oc_c30_2778)

lemma oc_c30_2779: "oc_sub oc_b30 2779"
  by (oc_eval oc_c30_2779)

lemma oc_c30_2780: "oc_sub oc_b30 2780"
  by (oc_eval oc_c30_2780)

lemma oc_c30_2781: "oc_sub oc_b30 2781"
  by (oc_eval oc_c30_2781)

lemma oc_c30_2782: "oc_sub oc_b30 2782"
  by (oc_eval oc_c30_2782)

lemma oc_c30_2783: "oc_sub oc_b30 2783"
  by (oc_eval oc_c30_2783)

lemma upt_c30_173: "[2768..<2784] = [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]"
  by (simp add: upt_rec)

lemma sec_c30_173: "\<forall>j\<in>{16 * 173..<16 * 173 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 173..<16 * 173 + 16}"
  then have "j \<in> set [2768..<2784]" unfolding set_upt by simp
  then have "j \<in> set [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]" unfolding upt_c30_173 .
  then show "oc_sub oc_b30 j" using oc_c30_2768 oc_c30_2769 oc_c30_2770 oc_c30_2771 oc_c30_2772 oc_c30_2773 oc_c30_2774 oc_c30_2775 oc_c30_2776 oc_c30_2777 oc_c30_2778 oc_c30_2779 oc_c30_2780 oc_c30_2781 oc_c30_2782 oc_c30_2783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
