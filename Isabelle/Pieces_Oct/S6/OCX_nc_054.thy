theory OCX_nc_054
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0864: "oc_sub None 864"
  by (oc_eval oc_nc_0864)

lemma oc_nc_0865: "oc_sub None 865"
  by (oc_eval oc_nc_0865)

lemma oc_nc_0866: "oc_sub None 866"
  by (oc_eval oc_nc_0866)

lemma oc_nc_0867: "oc_sub None 867"
  by (oc_eval oc_nc_0867)

lemma oc_nc_0868: "oc_sub None 868"
  by (oc_eval oc_nc_0868)

lemma oc_nc_0869: "oc_sub None 869"
  by (oc_eval oc_nc_0869)

lemma oc_nc_0870: "oc_sub None 870"
  by (oc_eval oc_nc_0870)

lemma oc_nc_0871: "oc_sub None 871"
  by (oc_eval oc_nc_0871)

lemma oc_nc_0872: "oc_sub None 872"
  by (oc_eval oc_nc_0872)

lemma oc_nc_0873: "oc_sub None 873"
  by (oc_eval oc_nc_0873)

lemma oc_nc_0874: "oc_sub None 874"
  by (oc_eval oc_nc_0874)

lemma oc_nc_0875: "oc_sub None 875"
  by (oc_eval oc_nc_0875)

lemma oc_nc_0876: "oc_sub None 876"
  by (oc_eval oc_nc_0876)

lemma oc_nc_0877: "oc_sub None 877"
  by (oc_eval oc_nc_0877)

lemma oc_nc_0878: "oc_sub None 878"
  by (oc_eval oc_nc_0878)

lemma oc_nc_0879: "oc_sub None 879"
  by (oc_eval oc_nc_0879)

lemma upt_nc_054: "[864..<880] = [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]"
  by (simp add: upt_rec)

lemma sec_nc_054: "\<forall>j\<in>{16 * 54..<16 * 54 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 54..<16 * 54 + 16}"
  then have "j \<in> set [864..<880]" unfolding set_upt by simp
  then have "j \<in> set [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]" unfolding upt_nc_054 .
  then show "oc_sub None j" using oc_nc_0864 oc_nc_0865 oc_nc_0866 oc_nc_0867 oc_nc_0868 oc_nc_0869 oc_nc_0870 oc_nc_0871 oc_nc_0872 oc_nc_0873 oc_nc_0874 oc_nc_0875 oc_nc_0876 oc_nc_0877 oc_nc_0878 oc_nc_0879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
