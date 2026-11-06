theory DCX_nc_048
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0768: "dc_sub None 768"
  by (dc_eval dc_nc_0768)

lemma dc_nc_0769: "dc_sub None 769"
  by (dc_eval dc_nc_0769)

lemma dc_nc_0770: "dc_sub None 770"
  by (dc_eval dc_nc_0770)

lemma dc_nc_0771: "dc_sub None 771"
  by (dc_eval dc_nc_0771)

lemma dc_nc_0772: "dc_sub None 772"
  by (dc_eval dc_nc_0772)

lemma dc_nc_0773: "dc_sub None 773"
  by (dc_eval dc_nc_0773)

lemma dc_nc_0774: "dc_sub None 774"
  by (dc_eval dc_nc_0774)

lemma dc_nc_0775: "dc_sub None 775"
  by (dc_eval dc_nc_0775)

lemma dc_nc_0776: "dc_sub None 776"
  by (dc_eval dc_nc_0776)

lemma dc_nc_0777: "dc_sub None 777"
  by (dc_eval dc_nc_0777)

lemma dc_nc_0778: "dc_sub None 778"
  by (dc_eval dc_nc_0778)

lemma dc_nc_0779: "dc_sub None 779"
  by (dc_eval dc_nc_0779)

lemma dc_nc_0780: "dc_sub None 780"
  by (dc_eval dc_nc_0780)

lemma dc_nc_0781: "dc_sub None 781"
  by (dc_eval dc_nc_0781)

lemma dc_nc_0782: "dc_sub None 782"
  by (dc_eval dc_nc_0782)

lemma dc_nc_0783: "dc_sub None 783"
  by (dc_eval dc_nc_0783)

lemma upt_nc_048: "[768..<784] = [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]"
  by (simp add: upt_rec)

lemma sec_nc_048: "\<forall>j\<in>{16 * 48..<16 * 48 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 48..<16 * 48 + 16}"
  then have "j \<in> set [768..<784]" unfolding set_upt by simp
  then have "j \<in> set [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]" unfolding upt_nc_048 .
  then show "dc_sub None j" using dc_nc_0768 dc_nc_0769 dc_nc_0770 dc_nc_0771 dc_nc_0772 dc_nc_0773 dc_nc_0774 dc_nc_0775 dc_nc_0776 dc_nc_0777 dc_nc_0778 dc_nc_0779 dc_nc_0780 dc_nc_0781 dc_nc_0782 dc_nc_0783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
