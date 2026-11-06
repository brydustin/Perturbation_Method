theory OCX_nc_173
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2768: "oc_sub None 2768"
  by (oc_eval oc_nc_2768)

lemma oc_nc_2769: "oc_sub None 2769"
  by (oc_eval oc_nc_2769)

lemma oc_nc_2770: "oc_sub None 2770"
  by (oc_eval oc_nc_2770)

lemma oc_nc_2771: "oc_sub None 2771"
  by (oc_eval oc_nc_2771)

lemma oc_nc_2772: "oc_sub None 2772"
  by (oc_eval oc_nc_2772)

lemma oc_nc_2773: "oc_sub None 2773"
  by (oc_eval oc_nc_2773)

lemma oc_nc_2774: "oc_sub None 2774"
  by (oc_eval oc_nc_2774)

lemma oc_nc_2775: "oc_sub None 2775"
  by (oc_eval oc_nc_2775)

lemma oc_nc_2776: "oc_sub None 2776"
  by (oc_eval oc_nc_2776)

lemma oc_nc_2777: "oc_sub None 2777"
  by (oc_eval oc_nc_2777)

lemma oc_nc_2778: "oc_sub None 2778"
  by (oc_eval oc_nc_2778)

lemma oc_nc_2779: "oc_sub None 2779"
  by (oc_eval oc_nc_2779)

lemma oc_nc_2780: "oc_sub None 2780"
  by (oc_eval oc_nc_2780)

lemma oc_nc_2781: "oc_sub None 2781"
  by (oc_eval oc_nc_2781)

lemma oc_nc_2782: "oc_sub None 2782"
  by (oc_eval oc_nc_2782)

lemma oc_nc_2783: "oc_sub None 2783"
  by (oc_eval oc_nc_2783)

lemma upt_nc_173: "[2768..<2784] = [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]"
  by (simp add: upt_rec)

lemma sec_nc_173: "\<forall>j\<in>{16 * 173..<16 * 173 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 173..<16 * 173 + 16}"
  then have "j \<in> set [2768..<2784]" unfolding set_upt by simp
  then have "j \<in> set [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]" unfolding upt_nc_173 .
  then show "oc_sub None j" using oc_nc_2768 oc_nc_2769 oc_nc_2770 oc_nc_2771 oc_nc_2772 oc_nc_2773 oc_nc_2774 oc_nc_2775 oc_nc_2776 oc_nc_2777 oc_nc_2778 oc_nc_2779 oc_nc_2780 oc_nc_2781 oc_nc_2782 oc_nc_2783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
