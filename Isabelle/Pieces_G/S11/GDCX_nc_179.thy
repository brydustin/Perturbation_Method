theory GDCX_nc_179
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2864: "gdc_sub None 2864"
  by (gdc_eval gdc_nc_2864)

lemma gdc_nc_2865: "gdc_sub None 2865"
  by (gdc_eval gdc_nc_2865)

lemma gdc_nc_2866: "gdc_sub None 2866"
  by (gdc_eval gdc_nc_2866)

lemma gdc_nc_2867: "gdc_sub None 2867"
  by (gdc_eval gdc_nc_2867)

lemma gdc_nc_2868: "gdc_sub None 2868"
  by (gdc_eval gdc_nc_2868)

lemma gdc_nc_2869: "gdc_sub None 2869"
  by (gdc_eval gdc_nc_2869)

lemma gdc_nc_2870: "gdc_sub None 2870"
  by (gdc_eval gdc_nc_2870)

lemma gdc_nc_2871: "gdc_sub None 2871"
  by (gdc_eval gdc_nc_2871)

lemma gdc_nc_2872: "gdc_sub None 2872"
  by (gdc_eval gdc_nc_2872)

lemma gdc_nc_2873: "gdc_sub None 2873"
  by (gdc_eval gdc_nc_2873)

lemma gdc_nc_2874: "gdc_sub None 2874"
  by (gdc_eval gdc_nc_2874)

lemma gdc_nc_2875: "gdc_sub None 2875"
  by (gdc_eval gdc_nc_2875)

lemma gdc_nc_2876: "gdc_sub None 2876"
  by (gdc_eval gdc_nc_2876)

lemma gdc_nc_2877: "gdc_sub None 2877"
  by (gdc_eval gdc_nc_2877)

lemma gdc_nc_2878: "gdc_sub None 2878"
  by (gdc_eval gdc_nc_2878)

lemma gdc_nc_2879: "gdc_sub None 2879"
  by (gdc_eval gdc_nc_2879)

lemma gupt_nc_179: "[2864..<2880] = [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]"
  by (simp add: upt_rec)

lemma gsec_nc_179: "\<forall>j\<in>{16 * 179..<16 * 179 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 179..<16 * 179 + 16}"
  then have "j \<in> set [2864..<2880]" unfolding set_upt by simp
  then have "j \<in> set [2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879]" unfolding gupt_nc_179 .
  then show "gdc_sub None j" using gdc_nc_2864 gdc_nc_2865 gdc_nc_2866 gdc_nc_2867 gdc_nc_2868 gdc_nc_2869 gdc_nc_2870 gdc_nc_2871 gdc_nc_2872 gdc_nc_2873 gdc_nc_2874 gdc_nc_2875 gdc_nc_2876 gdc_nc_2877 gdc_nc_2878 gdc_nc_2879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
