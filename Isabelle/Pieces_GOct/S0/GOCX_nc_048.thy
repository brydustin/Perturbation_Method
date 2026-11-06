theory GOCX_nc_048
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0768: "goc_sub None 768"
  by (goc_eval goc_nc_0768)

lemma goc_nc_0769: "goc_sub None 769"
  by (goc_eval goc_nc_0769)

lemma goc_nc_0770: "goc_sub None 770"
  by (goc_eval goc_nc_0770)

lemma goc_nc_0771: "goc_sub None 771"
  by (goc_eval goc_nc_0771)

lemma goc_nc_0772: "goc_sub None 772"
  by (goc_eval goc_nc_0772)

lemma goc_nc_0773: "goc_sub None 773"
  by (goc_eval goc_nc_0773)

lemma goc_nc_0774: "goc_sub None 774"
  by (goc_eval goc_nc_0774)

lemma goc_nc_0775: "goc_sub None 775"
  by (goc_eval goc_nc_0775)

lemma goc_nc_0776: "goc_sub None 776"
  by (goc_eval goc_nc_0776)

lemma goc_nc_0777: "goc_sub None 777"
  by (goc_eval goc_nc_0777)

lemma goc_nc_0778: "goc_sub None 778"
  by (goc_eval goc_nc_0778)

lemma goc_nc_0779: "goc_sub None 779"
  by (goc_eval goc_nc_0779)

lemma goc_nc_0780: "goc_sub None 780"
  by (goc_eval goc_nc_0780)

lemma goc_nc_0781: "goc_sub None 781"
  by (goc_eval goc_nc_0781)

lemma goc_nc_0782: "goc_sub None 782"
  by (goc_eval goc_nc_0782)

lemma goc_nc_0783: "goc_sub None 783"
  by (goc_eval goc_nc_0783)

lemma gupt_nc_048: "[768..<784] = [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]"
  by (simp add: upt_rec)

lemma gsec_nc_048: "\<forall>j\<in>{16 * 48..<16 * 48 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 48..<16 * 48 + 16}"
  then have "j \<in> set [768..<784]" unfolding set_upt by simp
  then have "j \<in> set [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]" unfolding gupt_nc_048 .
  then show "goc_sub None j" using goc_nc_0768 goc_nc_0769 goc_nc_0770 goc_nc_0771 goc_nc_0772 goc_nc_0773 goc_nc_0774 goc_nc_0775 goc_nc_0776 goc_nc_0777 goc_nc_0778 goc_nc_0779 goc_nc_0780 goc_nc_0781 goc_nc_0782 goc_nc_0783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
