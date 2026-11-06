theory GOCX_nc_166
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2656: "goc_sub None 2656"
  by (goc_eval goc_nc_2656)

lemma goc_nc_2657: "goc_sub None 2657"
  by (goc_eval goc_nc_2657)

lemma goc_nc_2658: "goc_sub None 2658"
  by (goc_eval goc_nc_2658)

lemma goc_nc_2659: "goc_sub None 2659"
  by (goc_eval goc_nc_2659)

lemma goc_nc_2660: "goc_sub None 2660"
  by (goc_eval goc_nc_2660)

lemma goc_nc_2661: "goc_sub None 2661"
  by (goc_eval goc_nc_2661)

lemma goc_nc_2662: "goc_sub None 2662"
  by (goc_eval goc_nc_2662)

lemma goc_nc_2663: "goc_sub None 2663"
  by (goc_eval goc_nc_2663)

lemma goc_nc_2664: "goc_sub None 2664"
  by (goc_eval goc_nc_2664)

lemma goc_nc_2665: "goc_sub None 2665"
  by (goc_eval goc_nc_2665)

lemma goc_nc_2666: "goc_sub None 2666"
  by (goc_eval goc_nc_2666)

lemma goc_nc_2667: "goc_sub None 2667"
  by (goc_eval goc_nc_2667)

lemma goc_nc_2668: "goc_sub None 2668"
  by (goc_eval goc_nc_2668)

lemma goc_nc_2669: "goc_sub None 2669"
  by (goc_eval goc_nc_2669)

lemma goc_nc_2670: "goc_sub None 2670"
  by (goc_eval goc_nc_2670)

lemma goc_nc_2671: "goc_sub None 2671"
  by (goc_eval goc_nc_2671)

lemma gupt_nc_166: "[2656..<2672] = [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]"
  by (simp add: upt_rec)

lemma gsec_nc_166: "\<forall>j\<in>{16 * 166..<16 * 166 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 166..<16 * 166 + 16}"
  then have "j \<in> set [2656..<2672]" unfolding set_upt by simp
  then have "j \<in> set [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]" unfolding gupt_nc_166 .
  then show "goc_sub None j" using goc_nc_2656 goc_nc_2657 goc_nc_2658 goc_nc_2659 goc_nc_2660 goc_nc_2661 goc_nc_2662 goc_nc_2663 goc_nc_2664 goc_nc_2665 goc_nc_2666 goc_nc_2667 goc_nc_2668 goc_nc_2669 goc_nc_2670 goc_nc_2671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
