theory DCX_nc_173
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2768: "dc_sub None 2768"
  by (dc_eval dc_nc_2768)

lemma dc_nc_2769: "dc_sub None 2769"
  by (dc_eval dc_nc_2769)

lemma dc_nc_2770: "dc_sub None 2770"
  by (dc_eval dc_nc_2770)

lemma dc_nc_2771: "dc_sub None 2771"
  by (dc_eval dc_nc_2771)

lemma dc_nc_2772: "dc_sub None 2772"
  by (dc_eval dc_nc_2772)

lemma dc_nc_2773: "dc_sub None 2773"
  by (dc_eval dc_nc_2773)

lemma dc_nc_2774: "dc_sub None 2774"
  by (dc_eval dc_nc_2774)

lemma dc_nc_2775: "dc_sub None 2775"
  by (dc_eval dc_nc_2775)

lemma dc_nc_2776: "dc_sub None 2776"
  by (dc_eval dc_nc_2776)

lemma dc_nc_2777: "dc_sub None 2777"
  by (dc_eval dc_nc_2777)

lemma dc_nc_2778: "dc_sub None 2778"
  by (dc_eval dc_nc_2778)

lemma dc_nc_2779: "dc_sub None 2779"
  by (dc_eval dc_nc_2779)

lemma dc_nc_2780: "dc_sub None 2780"
  by (dc_eval dc_nc_2780)

lemma dc_nc_2781: "dc_sub None 2781"
  by (dc_eval dc_nc_2781)

lemma dc_nc_2782: "dc_sub None 2782"
  by (dc_eval dc_nc_2782)

lemma dc_nc_2783: "dc_sub None 2783"
  by (dc_eval dc_nc_2783)

lemma upt_nc_173: "[2768..<2784] = [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]"
  by (simp add: upt_rec)

lemma sec_nc_173: "\<forall>j\<in>{16 * 173..<16 * 173 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 173..<16 * 173 + 16}"
  then have "j \<in> set [2768..<2784]" unfolding set_upt by simp
  then have "j \<in> set [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]" unfolding upt_nc_173 .
  then show "dc_sub None j" using dc_nc_2768 dc_nc_2769 dc_nc_2770 dc_nc_2771 dc_nc_2772 dc_nc_2773 dc_nc_2774 dc_nc_2775 dc_nc_2776 dc_nc_2777 dc_nc_2778 dc_nc_2779 dc_nc_2780 dc_nc_2781 dc_nc_2782 dc_nc_2783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
