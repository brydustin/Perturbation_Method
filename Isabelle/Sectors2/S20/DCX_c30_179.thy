theory DCX_c30_179
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2864: "dc_sub dc_b30 2864"
  by (dc_eval dc_c30_2864)

lemma dc_c30_2865: "dc_sub dc_b30 2865"
  by (dc_eval dc_c30_2865)

lemma dc_c30_2866: "dc_sub dc_b30 2866"
  by (dc_eval dc_c30_2866)

lemma dc_c30_2867: "dc_sub dc_b30 2867"
  by (dc_eval dc_c30_2867)

lemma dc_c30_2868: "dc_sub dc_b30 2868"
  by (dc_eval dc_c30_2868)

lemma dc_c30_2869: "dc_sub dc_b30 2869"
  by (dc_eval dc_c30_2869)

lemma dc_c30_2870: "dc_sub dc_b30 2870"
  by (dc_eval dc_c30_2870)

lemma dc_c30_2871: "dc_sub dc_b30 2871"
  by (dc_eval dc_c30_2871)

lemma dc_c30_2872: "dc_sub dc_b30 2872"
  by (dc_eval dc_c30_2872)

lemma dc_c30_2873: "dc_sub dc_b30 2873"
  by (dc_eval dc_c30_2873)

lemma dc_c30_2874: "dc_sub dc_b30 2874"
  by (dc_eval dc_c30_2874)

lemma dc_c30_2875: "dc_sub dc_b30 2875"
  by (dc_eval dc_c30_2875)

lemma dc_c30_2876: "dc_sub dc_b30 2876"
  by (dc_eval dc_c30_2876)

lemma dc_c30_2877: "dc_sub dc_b30 2877"
  by (dc_eval dc_c30_2877)

lemma dc_c30_2878: "dc_sub dc_b30 2878"
  by (dc_eval dc_c30_2878)

lemma dc_c30_2879: "dc_sub dc_b30 2879"
  by (dc_eval dc_c30_2879)

lemma upt_c30_179: "[2864..<2880] = [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]"
  by (simp add: upt_rec)

lemma sec_c30_179: "\<forall>j\<in>{16 * 179..<16 * 179 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 179..<16 * 179 + 16}"
  then have "j \<in> set [2864..<2880]" unfolding set_upt by simp
  then have "j \<in> set [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]" unfolding upt_c30_179 .
  then show "dc_sub dc_b30 j" using dc_c30_2864 dc_c30_2865 dc_c30_2866 dc_c30_2867 dc_c30_2868 dc_c30_2869 dc_c30_2870 dc_c30_2871 dc_c30_2872 dc_c30_2873 dc_c30_2874 dc_c30_2875 dc_c30_2876 dc_c30_2877 dc_c30_2878 dc_c30_2879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
