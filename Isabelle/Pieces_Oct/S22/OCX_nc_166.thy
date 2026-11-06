theory OCX_nc_166
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2656: "oc_sub None 2656"
  by (oc_eval oc_nc_2656)

lemma oc_nc_2657: "oc_sub None 2657"
  by (oc_eval oc_nc_2657)

lemma oc_nc_2658: "oc_sub None 2658"
  by (oc_eval oc_nc_2658)

lemma oc_nc_2659: "oc_sub None 2659"
  by (oc_eval oc_nc_2659)

lemma oc_nc_2660: "oc_sub None 2660"
  by (oc_eval oc_nc_2660)

lemma oc_nc_2661: "oc_sub None 2661"
  by (oc_eval oc_nc_2661)

lemma oc_nc_2662: "oc_sub None 2662"
  by (oc_eval oc_nc_2662)

lemma oc_nc_2663: "oc_sub None 2663"
  by (oc_eval oc_nc_2663)

lemma oc_nc_2664: "oc_sub None 2664"
  by (oc_eval oc_nc_2664)

lemma oc_nc_2665: "oc_sub None 2665"
  by (oc_eval oc_nc_2665)

lemma oc_nc_2666: "oc_sub None 2666"
  by (oc_eval oc_nc_2666)

lemma oc_nc_2667: "oc_sub None 2667"
  by (oc_eval oc_nc_2667)

lemma oc_nc_2668: "oc_sub None 2668"
  by (oc_eval oc_nc_2668)

lemma oc_nc_2669: "oc_sub None 2669"
  by (oc_eval oc_nc_2669)

lemma oc_nc_2670: "oc_sub None 2670"
  by (oc_eval oc_nc_2670)

lemma oc_nc_2671: "oc_sub None 2671"
  by (oc_eval oc_nc_2671)

lemma upt_nc_166: "[2656..<2672] = [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]"
  by (simp add: upt_rec)

lemma sec_nc_166: "\<forall>j\<in>{16 * 166..<16 * 166 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 166..<16 * 166 + 16}"
  then have "j \<in> set [2656..<2672]" unfolding set_upt by simp
  then have "j \<in> set [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]" unfolding upt_nc_166 .
  then show "oc_sub None j" using oc_nc_2656 oc_nc_2657 oc_nc_2658 oc_nc_2659 oc_nc_2660 oc_nc_2661 oc_nc_2662 oc_nc_2663 oc_nc_2664 oc_nc_2665 oc_nc_2666 oc_nc_2667 oc_nc_2668 oc_nc_2669 oc_nc_2670 oc_nc_2671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
