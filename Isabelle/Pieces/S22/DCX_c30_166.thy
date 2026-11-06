theory DCX_c30_166
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2656: "dc_sub dc_b30 2656"
  by (dc_eval dc_c30_2656)

lemma dc_c30_2657: "dc_sub dc_b30 2657"
  by (dc_eval dc_c30_2657)

lemma dc_c30_2658: "dc_sub dc_b30 2658"
  by (dc_eval dc_c30_2658)

lemma dc_c30_2659: "dc_sub dc_b30 2659"
  by (dc_eval dc_c30_2659)

lemma dc_c30_2660: "dc_sub dc_b30 2660"
  by (dc_eval dc_c30_2660)

lemma dc_c30_2661: "dc_sub dc_b30 2661"
  by (dc_eval dc_c30_2661)

lemma dc_c30_2662: "dc_sub dc_b30 2662"
  by (dc_eval dc_c30_2662)

lemma dc_c30_2663: "dc_sub dc_b30 2663"
  by (dc_eval dc_c30_2663)

lemma dc_c30_2664: "dc_sub dc_b30 2664"
  by (dc_eval dc_c30_2664)

lemma dc_c30_2665: "dc_sub dc_b30 2665"
  by (dc_eval dc_c30_2665)

lemma dc_c30_2666: "dc_sub dc_b30 2666"
  by (dc_eval dc_c30_2666)

lemma dc_c30_2667: "dc_sub dc_b30 2667"
  by (dc_eval dc_c30_2667)

lemma dc_c30_2668: "dc_sub dc_b30 2668"
  by (dc_eval dc_c30_2668)

lemma dc_c30_2669: "dc_sub dc_b30 2669"
  by (dc_eval dc_c30_2669)

lemma dc_c30_2670: "dc_sub dc_b30 2670"
  by (dc_eval dc_c30_2670)

lemma dc_c30_2671: "dc_sub dc_b30 2671"
  by (dc_eval dc_c30_2671)

lemma upt_c30_166: "[2656..<2672] = [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]"
  by (simp add: upt_rec)

lemma sec_c30_166: "\<forall>j\<in>{16 * 166..<16 * 166 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 166..<16 * 166 + 16}"
  then have "j \<in> set [2656..<2672]" unfolding set_upt by simp
  then have "j \<in> set [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]" unfolding upt_c30_166 .
  then show "dc_sub dc_b30 j" using dc_c30_2656 dc_c30_2657 dc_c30_2658 dc_c30_2659 dc_c30_2660 dc_c30_2661 dc_c30_2662 dc_c30_2663 dc_c30_2664 dc_c30_2665 dc_c30_2666 dc_c30_2667 dc_c30_2668 dc_c30_2669 dc_c30_2670 dc_c30_2671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
