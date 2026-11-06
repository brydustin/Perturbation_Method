theory OCX_c30_048
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0768: "oc_sub oc_b30 768"
  by (oc_eval oc_c30_0768)

lemma oc_c30_0769: "oc_sub oc_b30 769"
  by (oc_eval oc_c30_0769)

lemma oc_c30_0770: "oc_sub oc_b30 770"
  by (oc_eval oc_c30_0770)

lemma oc_c30_0771: "oc_sub oc_b30 771"
  by (oc_eval oc_c30_0771)

lemma oc_c30_0772: "oc_sub oc_b30 772"
  by (oc_eval oc_c30_0772)

lemma oc_c30_0773: "oc_sub oc_b30 773"
  by (oc_eval oc_c30_0773)

lemma oc_c30_0774: "oc_sub oc_b30 774"
  by (oc_eval oc_c30_0774)

lemma oc_c30_0775: "oc_sub oc_b30 775"
  by (oc_eval oc_c30_0775)

lemma oc_c30_0776: "oc_sub oc_b30 776"
  by (oc_eval oc_c30_0776)

lemma oc_c30_0777: "oc_sub oc_b30 777"
  by (oc_eval oc_c30_0777)

lemma oc_c30_0778: "oc_sub oc_b30 778"
  by (oc_eval oc_c30_0778)

lemma oc_c30_0779: "oc_sub oc_b30 779"
  by (oc_eval oc_c30_0779)

lemma oc_c30_0780: "oc_sub oc_b30 780"
  by (oc_eval oc_c30_0780)

lemma oc_c30_0781: "oc_sub oc_b30 781"
  by (oc_eval oc_c30_0781)

lemma oc_c30_0782: "oc_sub oc_b30 782"
  by (oc_eval oc_c30_0782)

lemma oc_c30_0783: "oc_sub oc_b30 783"
  by (oc_eval oc_c30_0783)

lemma upt_c30_048: "[768..<784] = [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]"
  by (simp add: upt_rec)

lemma sec_c30_048: "\<forall>j\<in>{16 * 48..<16 * 48 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 48..<16 * 48 + 16}"
  then have "j \<in> set [768..<784]" unfolding set_upt by simp
  then have "j \<in> set [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]" unfolding upt_c30_048 .
  then show "oc_sub oc_b30 j" using oc_c30_0768 oc_c30_0769 oc_c30_0770 oc_c30_0771 oc_c30_0772 oc_c30_0773 oc_c30_0774 oc_c30_0775 oc_c30_0776 oc_c30_0777 oc_c30_0778 oc_c30_0779 oc_c30_0780 oc_c30_0781 oc_c30_0782 oc_c30_0783
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
