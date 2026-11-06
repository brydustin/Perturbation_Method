theory GOCX_nc_173
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2768: "goc_sub None 2768"
  by (goc_eval goc_nc_2768)

lemma goc_nc_2769: "goc_sub None 2769"
  by (goc_eval goc_nc_2769)

lemma goc_nc_2770: "goc_sub None 2770"
  by (goc_eval goc_nc_2770)

lemma goc_nc_2771: "goc_sub None 2771"
  by (goc_eval goc_nc_2771)

lemma goc_nc_2772: "goc_sub None 2772"
  by (goc_eval goc_nc_2772)

lemma goc_nc_2773: "goc_sub None 2773"
  by (goc_eval goc_nc_2773)

lemma goc_nc_2774: "goc_sub None 2774"
  by (goc_eval goc_nc_2774)

lemma goc_nc_2775: "goc_sub None 2775"
  by (goc_eval goc_nc_2775)

lemma goc_nc_2776: "goc_sub None 2776"
  by (goc_eval goc_nc_2776)

lemma goc_nc_2777: "goc_sub None 2777"
  by (goc_eval goc_nc_2777)

lemma goc_nc_2778: "goc_sub None 2778"
  by (goc_eval goc_nc_2778)

lemma goc_nc_2779: "goc_sub None 2779"
  by (goc_eval goc_nc_2779)

lemma goc_nc_2780: "goc_sub None 2780"
  by (goc_eval goc_nc_2780)

lemma goc_nc_2781: "goc_sub None 2781"
  by (goc_eval goc_nc_2781)

lemma goc_nc_2782: "goc_sub None 2782"
  by (goc_eval goc_nc_2782)

lemma goc_nc_2783: "goc_sub None 2783"
  by (goc_eval goc_nc_2783)

lemma gupt_nc_173: "[2768..<2784] = [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]"
  by (simp add: upt_rec)

lemma gsec_nc_173: "\<forall>j\<in>{16 * 173..<16 * 173 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 173..<16 * 173 + 16}"
  then have "j \<in> set [2768..<2784]" unfolding set_upt by simp
  then have "j \<in> set [2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783]" unfolding gupt_nc_173 .
  then show "goc_sub None j" using goc_nc_2768 goc_nc_2769 goc_nc_2770 goc_nc_2771 goc_nc_2772 goc_nc_2773 goc_nc_2774 goc_nc_2775 goc_nc_2776 goc_nc_2777 goc_nc_2778 goc_nc_2779 goc_nc_2780 goc_nc_2781 goc_nc_2782 goc_nc_2783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
