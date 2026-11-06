theory GDCX_nc_166
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2656: "gdc_sub None 2656"
  by (gdc_eval gdc_nc_2656)

lemma gdc_nc_2657: "gdc_sub None 2657"
  by (gdc_eval gdc_nc_2657)

lemma gdc_nc_2658: "gdc_sub None 2658"
  by (gdc_eval gdc_nc_2658)

lemma gdc_nc_2659: "gdc_sub None 2659"
  by (gdc_eval gdc_nc_2659)

lemma gdc_nc_2660: "gdc_sub None 2660"
  by (gdc_eval gdc_nc_2660)

lemma gdc_nc_2661: "gdc_sub None 2661"
  by (gdc_eval gdc_nc_2661)

lemma gdc_nc_2662: "gdc_sub None 2662"
  by (gdc_eval gdc_nc_2662)

lemma gdc_nc_2663: "gdc_sub None 2663"
  by (gdc_eval gdc_nc_2663)

lemma gdc_nc_2664: "gdc_sub None 2664"
  by (gdc_eval gdc_nc_2664)

lemma gdc_nc_2665: "gdc_sub None 2665"
  by (gdc_eval gdc_nc_2665)

lemma gdc_nc_2666: "gdc_sub None 2666"
  by (gdc_eval gdc_nc_2666)

lemma gdc_nc_2667: "gdc_sub None 2667"
  by (gdc_eval gdc_nc_2667)

lemma gdc_nc_2668: "gdc_sub None 2668"
  by (gdc_eval gdc_nc_2668)

lemma gdc_nc_2669: "gdc_sub None 2669"
  by (gdc_eval gdc_nc_2669)

lemma gdc_nc_2670: "gdc_sub None 2670"
  by (gdc_eval gdc_nc_2670)

lemma gdc_nc_2671: "gdc_sub None 2671"
  by (gdc_eval gdc_nc_2671)

lemma gupt_nc_166: "[2656..<2672] = [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]"
  by (simp add: upt_rec)

lemma gsec_nc_166: "\<forall>j\<in>{16 * 166..<16 * 166 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 166..<16 * 166 + 16}"
  then have "j \<in> set [2656..<2672]" unfolding set_upt by simp
  then have "j \<in> set [2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671]" unfolding gupt_nc_166 .
  then show "gdc_sub None j" using gdc_nc_2656 gdc_nc_2657 gdc_nc_2658 gdc_nc_2659 gdc_nc_2660 gdc_nc_2661 gdc_nc_2662 gdc_nc_2663 gdc_nc_2664 gdc_nc_2665 gdc_nc_2666 gdc_nc_2667 gdc_nc_2668 gdc_nc_2669 gdc_nc_2670 gdc_nc_2671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
