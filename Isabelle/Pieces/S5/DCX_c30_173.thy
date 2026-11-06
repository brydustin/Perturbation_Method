theory DCX_c30_173
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2768: "dc_sub dc_b30 2768"
  by (dc_eval dc_c30_2768)

lemma dc_c30_2769: "dc_sub dc_b30 2769"
  by (dc_eval dc_c30_2769)

lemma dc_c30_2770: "dc_sub dc_b30 2770"
  by (dc_eval dc_c30_2770)

lemma dc_c30_2771: "dc_sub dc_b30 2771"
  by (dc_eval dc_c30_2771)

lemma dc_c30_2772: "dc_sub dc_b30 2772"
  by (dc_eval dc_c30_2772)

lemma dc_c30_2773: "dc_sub dc_b30 2773"
  by (dc_eval dc_c30_2773)

lemma dc_c30_2774: "dc_sub dc_b30 2774"
  by (dc_eval dc_c30_2774)

lemma dc_c30_2775: "dc_sub dc_b30 2775"
  by (dc_eval dc_c30_2775)

lemma dc_c30_2776: "dc_sub dc_b30 2776"
  by (dc_eval dc_c30_2776)

lemma dc_c30_2777: "dc_sub dc_b30 2777"
  by (dc_eval dc_c30_2777)

lemma dc_c30_2778: "dc_sub dc_b30 2778"
  by (dc_eval dc_c30_2778)

lemma dc_c30_2779: "dc_sub dc_b30 2779"
  by (dc_eval dc_c30_2779)

lemma dc_c30_2780: "dc_sub dc_b30 2780"
  by (dc_eval dc_c30_2780)

lemma dc_c30_2781: "dc_sub dc_b30 2781"
  by (dc_eval dc_c30_2781)

lemma dc_c30_2782: "dc_sub dc_b30 2782"
  by (dc_eval dc_c30_2782)

lemma dc_c30_2783: "dc_sub dc_b30 2783"
  by (dc_eval dc_c30_2783)

lemma upt_c30_173: "[2768..<2784] = [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]"
  by (simp add: upt_rec)

lemma sec_c30_173: "\<forall>j\<in>{16 * 173..<16 * 173 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 173..<16 * 173 + 16}"
  then have "j \<in> set [2768..<2784]" unfolding set_upt by simp
  then have "j \<in> set [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]" unfolding upt_c30_173 .
  then show "dc_sub dc_b30 j" using dc_c30_2768 dc_c30_2769 dc_c30_2770 dc_c30_2771 dc_c30_2772 dc_c30_2773 dc_c30_2774 dc_c30_2775 dc_c30_2776 dc_c30_2777 dc_c30_2778 dc_c30_2779 dc_c30_2780 dc_c30_2781 dc_c30_2782 dc_c30_2783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
