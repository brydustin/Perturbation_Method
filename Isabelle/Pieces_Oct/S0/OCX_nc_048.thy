theory OCX_nc_048
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0768: "oc_sub None 768"
  by (oc_eval oc_nc_0768)

lemma oc_nc_0769: "oc_sub None 769"
  by (oc_eval oc_nc_0769)

lemma oc_nc_0770: "oc_sub None 770"
  by (oc_eval oc_nc_0770)

lemma oc_nc_0771: "oc_sub None 771"
  by (oc_eval oc_nc_0771)

lemma oc_nc_0772: "oc_sub None 772"
  by (oc_eval oc_nc_0772)

lemma oc_nc_0773: "oc_sub None 773"
  by (oc_eval oc_nc_0773)

lemma oc_nc_0774: "oc_sub None 774"
  by (oc_eval oc_nc_0774)

lemma oc_nc_0775: "oc_sub None 775"
  by (oc_eval oc_nc_0775)

lemma oc_nc_0776: "oc_sub None 776"
  by (oc_eval oc_nc_0776)

lemma oc_nc_0777: "oc_sub None 777"
  by (oc_eval oc_nc_0777)

lemma oc_nc_0778: "oc_sub None 778"
  by (oc_eval oc_nc_0778)

lemma oc_nc_0779: "oc_sub None 779"
  by (oc_eval oc_nc_0779)

lemma oc_nc_0780: "oc_sub None 780"
  by (oc_eval oc_nc_0780)

lemma oc_nc_0781: "oc_sub None 781"
  by (oc_eval oc_nc_0781)

lemma oc_nc_0782: "oc_sub None 782"
  by (oc_eval oc_nc_0782)

lemma oc_nc_0783: "oc_sub None 783"
  by (oc_eval oc_nc_0783)

lemma upt_nc_048: "[768..<784] = [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]"
  by (simp add: upt_rec)

lemma sec_nc_048: "\<forall>j\<in>{16 * 48..<16 * 48 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 48..<16 * 48 + 16}"
  then have "j \<in> set [768..<784]" unfolding set_upt by simp
  then have "j \<in> set [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]" unfolding upt_nc_048 .
  then show "oc_sub None j" using oc_nc_0768 oc_nc_0769 oc_nc_0770 oc_nc_0771 oc_nc_0772 oc_nc_0773 oc_nc_0774 oc_nc_0775 oc_nc_0776 oc_nc_0777 oc_nc_0778 oc_nc_0779 oc_nc_0780 oc_nc_0781 oc_nc_0782 oc_nc_0783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
