theory GDCX_nc_173
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2768: "gdc_sub None 2768"
  by (gdc_eval gdc_nc_2768)

lemma gdc_nc_2769: "gdc_sub None 2769"
  by (gdc_eval gdc_nc_2769)

lemma gdc_nc_2770: "gdc_sub None 2770"
  by (gdc_eval gdc_nc_2770)

lemma gdc_nc_2771: "gdc_sub None 2771"
  by (gdc_eval gdc_nc_2771)

lemma gdc_nc_2772: "gdc_sub None 2772"
  by (gdc_eval gdc_nc_2772)

lemma gdc_nc_2773: "gdc_sub None 2773"
  by (gdc_eval gdc_nc_2773)

lemma gdc_nc_2774: "gdc_sub None 2774"
  by (gdc_eval gdc_nc_2774)

lemma gdc_nc_2775: "gdc_sub None 2775"
  by (gdc_eval gdc_nc_2775)

lemma gdc_nc_2776: "gdc_sub None 2776"
  by (gdc_eval gdc_nc_2776)

lemma gdc_nc_2777: "gdc_sub None 2777"
  by (gdc_eval gdc_nc_2777)

lemma gdc_nc_2778: "gdc_sub None 2778"
  by (gdc_eval gdc_nc_2778)

lemma gdc_nc_2779: "gdc_sub None 2779"
  by (gdc_eval gdc_nc_2779)

lemma gdc_nc_2780: "gdc_sub None 2780"
  by (gdc_eval gdc_nc_2780)

lemma gdc_nc_2781: "gdc_sub None 2781"
  by (gdc_eval gdc_nc_2781)

lemma gdc_nc_2782: "gdc_sub None 2782"
  by (gdc_eval gdc_nc_2782)

lemma gdc_nc_2783: "gdc_sub None 2783"
  by (gdc_eval gdc_nc_2783)

lemma gupt_nc_173: "[2768..<2784] = [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]"
  by (simp add: upt_rec)

lemma gsec_nc_173: "\<forall>j\<in>{16 * 173..<16 * 173 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 173..<16 * 173 + 16}"
  then have "j \<in> set [2768..<2784]" unfolding set_upt by simp
  then have "j \<in> set [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]" unfolding gupt_nc_173 .
  then show "gdc_sub None j" using gdc_nc_2768 gdc_nc_2769 gdc_nc_2770 gdc_nc_2771 gdc_nc_2772 gdc_nc_2773 gdc_nc_2774 gdc_nc_2775 gdc_nc_2776 gdc_nc_2777 gdc_nc_2778 gdc_nc_2779 gdc_nc_2780 gdc_nc_2781 gdc_nc_2782 gdc_nc_2783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
