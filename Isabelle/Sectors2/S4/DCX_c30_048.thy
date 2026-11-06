theory DCX_c30_048
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0768: "dc_sub dc_b30 768"
  by (dc_eval dc_c30_0768)

lemma dc_c30_0769: "dc_sub dc_b30 769"
  by (dc_eval dc_c30_0769)

lemma dc_c30_0770: "dc_sub dc_b30 770"
  by (dc_eval dc_c30_0770)

lemma dc_c30_0771: "dc_sub dc_b30 771"
  by (dc_eval dc_c30_0771)

lemma dc_c30_0772: "dc_sub dc_b30 772"
  by (dc_eval dc_c30_0772)

lemma dc_c30_0773: "dc_sub dc_b30 773"
  by (dc_eval dc_c30_0773)

lemma dc_c30_0774: "dc_sub dc_b30 774"
  by (dc_eval dc_c30_0774)

lemma dc_c30_0775: "dc_sub dc_b30 775"
  by (dc_eval dc_c30_0775)

lemma dc_c30_0776: "dc_sub dc_b30 776"
  by (dc_eval dc_c30_0776)

lemma dc_c30_0777: "dc_sub dc_b30 777"
  by (dc_eval dc_c30_0777)

lemma dc_c30_0778: "dc_sub dc_b30 778"
  by (dc_eval dc_c30_0778)

lemma dc_c30_0779: "dc_sub dc_b30 779"
  by (dc_eval dc_c30_0779)

lemma dc_c30_0780: "dc_sub dc_b30 780"
  by (dc_eval dc_c30_0780)

lemma dc_c30_0781: "dc_sub dc_b30 781"
  by (dc_eval dc_c30_0781)

lemma dc_c30_0782: "dc_sub dc_b30 782"
  by (dc_eval dc_c30_0782)

lemma dc_c30_0783: "dc_sub dc_b30 783"
  by (dc_eval dc_c30_0783)

lemma upt_c30_048: "[768..<784] = [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]"
  by (simp add: upt_rec)

lemma sec_c30_048: "\<forall>j\<in>{16 * 48..<16 * 48 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 48..<16 * 48 + 16}"
  then have "j \<in> set [768..<784]" unfolding set_upt by simp
  then have "j \<in> set [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]" unfolding upt_c30_048 .
  then show "dc_sub dc_b30 j" using dc_c30_0768 dc_c30_0769 dc_c30_0770 dc_c30_0771 dc_c30_0772 dc_c30_0773 dc_c30_0774 dc_c30_0775 dc_c30_0776 dc_c30_0777 dc_c30_0778 dc_c30_0779 dc_c30_0780 dc_c30_0781 dc_c30_0782 dc_c30_0783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
