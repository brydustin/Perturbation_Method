theory GOCX_nc_179
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2864: "goc_sub None 2864"
  by (goc_eval goc_nc_2864)

lemma goc_nc_2865: "goc_sub None 2865"
  by (goc_eval goc_nc_2865)

lemma goc_nc_2866: "goc_sub None 2866"
  by (goc_eval goc_nc_2866)

lemma goc_nc_2867: "goc_sub None 2867"
  by (goc_eval goc_nc_2867)

lemma goc_nc_2868: "goc_sub None 2868"
  by (goc_eval goc_nc_2868)

lemma goc_nc_2869: "goc_sub None 2869"
  by (goc_eval goc_nc_2869)

lemma goc_nc_2870: "goc_sub None 2870"
  by (goc_eval goc_nc_2870)

lemma goc_nc_2871: "goc_sub None 2871"
  by (goc_eval goc_nc_2871)

lemma goc_nc_2872: "goc_sub None 2872"
  by (goc_eval goc_nc_2872)

lemma goc_nc_2873: "goc_sub None 2873"
  by (goc_eval goc_nc_2873)

lemma goc_nc_2874: "goc_sub None 2874"
  by (goc_eval goc_nc_2874)

lemma goc_nc_2875: "goc_sub None 2875"
  by (goc_eval goc_nc_2875)

lemma goc_nc_2876: "goc_sub None 2876"
  by (goc_eval goc_nc_2876)

lemma goc_nc_2877: "goc_sub None 2877"
  by (goc_eval goc_nc_2877)

lemma goc_nc_2878: "goc_sub None 2878"
  by (goc_eval goc_nc_2878)

lemma goc_nc_2879: "goc_sub None 2879"
  by (goc_eval goc_nc_2879)

lemma gupt_nc_179: "[2864..<2880] = [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]"
  by (simp add: upt_rec)

lemma gsec_nc_179: "\<forall>j\<in>{16 * 179..<16 * 179 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 179..<16 * 179 + 16}"
  then have "j \<in> set [2864..<2880]" unfolding set_upt by simp
  then have "j \<in> set [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]" unfolding gupt_nc_179 .
  then show "goc_sub None j" using goc_nc_2864 goc_nc_2865 goc_nc_2866 goc_nc_2867 goc_nc_2868 goc_nc_2869 goc_nc_2870 goc_nc_2871 goc_nc_2872 goc_nc_2873 goc_nc_2874 goc_nc_2875 goc_nc_2876 goc_nc_2877 goc_nc_2878 goc_nc_2879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
