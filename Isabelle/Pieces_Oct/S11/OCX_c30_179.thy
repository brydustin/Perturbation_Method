theory OCX_c30_179
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2864: "oc_sub oc_b30 2864"
  by (oc_eval oc_c30_2864)

lemma oc_c30_2865: "oc_sub oc_b30 2865"
  by (oc_eval oc_c30_2865)

lemma oc_c30_2866: "oc_sub oc_b30 2866"
  by (oc_eval oc_c30_2866)

lemma oc_c30_2867: "oc_sub oc_b30 2867"
  by (oc_eval oc_c30_2867)

lemma oc_c30_2868: "oc_sub oc_b30 2868"
  by (oc_eval oc_c30_2868)

lemma oc_c30_2869: "oc_sub oc_b30 2869"
  by (oc_eval oc_c30_2869)

lemma oc_c30_2870: "oc_sub oc_b30 2870"
  by (oc_eval oc_c30_2870)

lemma oc_c30_2871: "oc_sub oc_b30 2871"
  by (oc_eval oc_c30_2871)

lemma oc_c30_2872: "oc_sub oc_b30 2872"
  by (oc_eval oc_c30_2872)

lemma oc_c30_2873: "oc_sub oc_b30 2873"
  by (oc_eval oc_c30_2873)

lemma oc_c30_2874: "oc_sub oc_b30 2874"
  by (oc_eval oc_c30_2874)

lemma oc_c30_2875: "oc_sub oc_b30 2875"
  by (oc_eval oc_c30_2875)

lemma oc_c30_2876: "oc_sub oc_b30 2876"
  by (oc_eval oc_c30_2876)

lemma oc_c30_2877: "oc_sub oc_b30 2877"
  by (oc_eval oc_c30_2877)

lemma oc_c30_2878: "oc_sub oc_b30 2878"
  by (oc_eval oc_c30_2878)

lemma oc_c30_2879: "oc_sub oc_b30 2879"
  by (oc_eval oc_c30_2879)

lemma upt_c30_179: "[2864..<2880] = [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]"
  by (simp add: upt_rec)

lemma sec_c30_179: "\<forall>j\<in>{16 * 179..<16 * 179 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 179..<16 * 179 + 16}"
  then have "j \<in> set [2864..<2880]" unfolding set_upt by simp
  then have "j \<in> set [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]" unfolding upt_c30_179 .
  then show "oc_sub oc_b30 j" using oc_c30_2864 oc_c30_2865 oc_c30_2866 oc_c30_2867 oc_c30_2868 oc_c30_2869 oc_c30_2870 oc_c30_2871 oc_c30_2872 oc_c30_2873 oc_c30_2874 oc_c30_2875 oc_c30_2876 oc_c30_2877 oc_c30_2878 oc_c30_2879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
