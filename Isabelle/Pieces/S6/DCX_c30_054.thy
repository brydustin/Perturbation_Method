theory DCX_c30_054
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0864: "dc_sub dc_b30 864"
  by (dc_eval dc_c30_0864)

lemma dc_c30_0865: "dc_sub dc_b30 865"
  by (dc_eval dc_c30_0865)

lemma dc_c30_0866: "dc_sub dc_b30 866"
  by (dc_eval dc_c30_0866)

lemma dc_c30_0867: "dc_sub dc_b30 867"
  by (dc_eval dc_c30_0867)

lemma dc_c30_0868: "dc_sub dc_b30 868"
  by (dc_eval dc_c30_0868)

lemma dc_c30_0869: "dc_sub dc_b30 869"
  by (dc_eval dc_c30_0869)

lemma dc_c30_0870: "dc_sub dc_b30 870"
  by (dc_eval dc_c30_0870)

lemma dc_c30_0871: "dc_sub dc_b30 871"
  by (dc_eval dc_c30_0871)

lemma dc_c30_0872: "dc_sub dc_b30 872"
  by (dc_eval dc_c30_0872)

lemma dc_c30_0873: "dc_sub dc_b30 873"
  by (dc_eval dc_c30_0873)

lemma dc_c30_0874: "dc_sub dc_b30 874"
  by (dc_eval dc_c30_0874)

lemma dc_c30_0875: "dc_sub dc_b30 875"
  by (dc_eval dc_c30_0875)

lemma dc_c30_0876: "dc_sub dc_b30 876"
  by (dc_eval dc_c30_0876)

lemma dc_c30_0877: "dc_sub dc_b30 877"
  by (dc_eval dc_c30_0877)

lemma dc_c30_0878: "dc_sub dc_b30 878"
  by (dc_eval dc_c30_0878)

lemma dc_c30_0879: "dc_sub dc_b30 879"
  by (dc_eval dc_c30_0879)

lemma upt_c30_054: "[864..<880] = [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]"
  by (simp add: upt_rec)

lemma sec_c30_054: "\<forall>j\<in>{16 * 54..<16 * 54 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 54..<16 * 54 + 16}"
  then have "j \<in> set [864..<880]" unfolding set_upt by simp
  then have "j \<in> set [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]" unfolding upt_c30_054 .
  then show "dc_sub dc_b30 j" using dc_c30_0864 dc_c30_0865 dc_c30_0866 dc_c30_0867 dc_c30_0868 dc_c30_0869 dc_c30_0870 dc_c30_0871 dc_c30_0872 dc_c30_0873 dc_c30_0874 dc_c30_0875 dc_c30_0876 dc_c30_0877 dc_c30_0878 dc_c30_0879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
