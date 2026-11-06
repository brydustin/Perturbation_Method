theory GDCX_nc_048
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0768: "gdc_sub None 768"
  by (gdc_eval gdc_nc_0768)

lemma gdc_nc_0769: "gdc_sub None 769"
  by (gdc_eval gdc_nc_0769)

lemma gdc_nc_0770: "gdc_sub None 770"
  by (gdc_eval gdc_nc_0770)

lemma gdc_nc_0771: "gdc_sub None 771"
  by (gdc_eval gdc_nc_0771)

lemma gdc_nc_0772: "gdc_sub None 772"
  by (gdc_eval gdc_nc_0772)

lemma gdc_nc_0773: "gdc_sub None 773"
  by (gdc_eval gdc_nc_0773)

lemma gdc_nc_0774: "gdc_sub None 774"
  by (gdc_eval gdc_nc_0774)

lemma gdc_nc_0775: "gdc_sub None 775"
  by (gdc_eval gdc_nc_0775)

lemma gdc_nc_0776: "gdc_sub None 776"
  by (gdc_eval gdc_nc_0776)

lemma gdc_nc_0777: "gdc_sub None 777"
  by (gdc_eval gdc_nc_0777)

lemma gdc_nc_0778: "gdc_sub None 778"
  by (gdc_eval gdc_nc_0778)

lemma gdc_nc_0779: "gdc_sub None 779"
  by (gdc_eval gdc_nc_0779)

lemma gdc_nc_0780: "gdc_sub None 780"
  by (gdc_eval gdc_nc_0780)

lemma gdc_nc_0781: "gdc_sub None 781"
  by (gdc_eval gdc_nc_0781)

lemma gdc_nc_0782: "gdc_sub None 782"
  by (gdc_eval gdc_nc_0782)

lemma gdc_nc_0783: "gdc_sub None 783"
  by (gdc_eval gdc_nc_0783)

lemma gupt_nc_048: "[768..<784] = [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]"
  by (simp add: upt_rec)

lemma gsec_nc_048: "\<forall>j\<in>{16 * 48..<16 * 48 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 48..<16 * 48 + 16}"
  then have "j \<in> set [768..<784]" unfolding set_upt by simp
  then have "j \<in> set [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]" unfolding gupt_nc_048 .
  then show "gdc_sub None j" using gdc_nc_0768 gdc_nc_0769 gdc_nc_0770 gdc_nc_0771 gdc_nc_0772 gdc_nc_0773 gdc_nc_0774 gdc_nc_0775 gdc_nc_0776 gdc_nc_0777 gdc_nc_0778 gdc_nc_0779 gdc_nc_0780 gdc_nc_0781 gdc_nc_0782 gdc_nc_0783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
