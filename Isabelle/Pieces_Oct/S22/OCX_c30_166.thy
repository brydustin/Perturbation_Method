theory OCX_c30_166
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2656: "oc_sub oc_b30 2656"
  by (oc_eval oc_c30_2656)

lemma oc_c30_2657: "oc_sub oc_b30 2657"
  by (oc_eval oc_c30_2657)

lemma oc_c30_2658: "oc_sub oc_b30 2658"
  by (oc_eval oc_c30_2658)

lemma oc_c30_2659: "oc_sub oc_b30 2659"
  by (oc_eval oc_c30_2659)

lemma oc_c30_2660: "oc_sub oc_b30 2660"
  by (oc_eval oc_c30_2660)

lemma oc_c30_2661: "oc_sub oc_b30 2661"
  by (oc_eval oc_c30_2661)

lemma oc_c30_2662: "oc_sub oc_b30 2662"
  by (oc_eval oc_c30_2662)

lemma oc_c30_2663: "oc_sub oc_b30 2663"
  by (oc_eval oc_c30_2663)

lemma oc_c30_2664: "oc_sub oc_b30 2664"
  by (oc_eval oc_c30_2664)

lemma oc_c30_2665: "oc_sub oc_b30 2665"
  by (oc_eval oc_c30_2665)

lemma oc_c30_2666: "oc_sub oc_b30 2666"
  by (oc_eval oc_c30_2666)

lemma oc_c30_2667: "oc_sub oc_b30 2667"
  by (oc_eval oc_c30_2667)

lemma oc_c30_2668: "oc_sub oc_b30 2668"
  by (oc_eval oc_c30_2668)

lemma oc_c30_2669: "oc_sub oc_b30 2669"
  by (oc_eval oc_c30_2669)

lemma oc_c30_2670: "oc_sub oc_b30 2670"
  by (oc_eval oc_c30_2670)

lemma oc_c30_2671: "oc_sub oc_b30 2671"
  by (oc_eval oc_c30_2671)

lemma upt_c30_166: "[2656..<2672] = [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]"
  by (simp add: upt_rec)

lemma sec_c30_166: "\<forall>j\<in>{16 * 166..<16 * 166 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 166..<16 * 166 + 16}"
  then have "j \<in> set [2656..<2672]" unfolding set_upt by simp
  then have "j \<in> set [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]" unfolding upt_c30_166 .
  then show "oc_sub oc_b30 j" using oc_c30_2656 oc_c30_2657 oc_c30_2658 oc_c30_2659 oc_c30_2660 oc_c30_2661 oc_c30_2662 oc_c30_2663 oc_c30_2664 oc_c30_2665 oc_c30_2666 oc_c30_2667 oc_c30_2668 oc_c30_2669 oc_c30_2670 oc_c30_2671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
