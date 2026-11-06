theory OCX_c30_054
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0864: "oc_sub oc_b30 864"
  by (oc_eval oc_c30_0864)

lemma oc_c30_0865: "oc_sub oc_b30 865"
  by (oc_eval oc_c30_0865)

lemma oc_c30_0866: "oc_sub oc_b30 866"
  by (oc_eval oc_c30_0866)

lemma oc_c30_0867: "oc_sub oc_b30 867"
  by (oc_eval oc_c30_0867)

lemma oc_c30_0868: "oc_sub oc_b30 868"
  by (oc_eval oc_c30_0868)

lemma oc_c30_0869: "oc_sub oc_b30 869"
  by (oc_eval oc_c30_0869)

lemma oc_c30_0870: "oc_sub oc_b30 870"
  by (oc_eval oc_c30_0870)

lemma oc_c30_0871: "oc_sub oc_b30 871"
  by (oc_eval oc_c30_0871)

lemma oc_c30_0872: "oc_sub oc_b30 872"
  by (oc_eval oc_c30_0872)

lemma oc_c30_0873: "oc_sub oc_b30 873"
  by (oc_eval oc_c30_0873)

lemma oc_c30_0874: "oc_sub oc_b30 874"
  by (oc_eval oc_c30_0874)

lemma oc_c30_0875: "oc_sub oc_b30 875"
  by (oc_eval oc_c30_0875)

lemma oc_c30_0876: "oc_sub oc_b30 876"
  by (oc_eval oc_c30_0876)

lemma oc_c30_0877: "oc_sub oc_b30 877"
  by (oc_eval oc_c30_0877)

lemma oc_c30_0878: "oc_sub oc_b30 878"
  by (oc_eval oc_c30_0878)

lemma oc_c30_0879: "oc_sub oc_b30 879"
  by (oc_eval oc_c30_0879)

lemma upt_c30_054: "[864..<880] = [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]"
  by (simp add: upt_rec)

lemma sec_c30_054: "\<forall>j\<in>{16 * 54..<16 * 54 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 54..<16 * 54 + 16}"
  then have "j \<in> set [864..<880]" unfolding set_upt by simp
  then have "j \<in> set [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]" unfolding upt_c30_054 .
  then show "oc_sub oc_b30 j" using oc_c30_0864 oc_c30_0865 oc_c30_0866 oc_c30_0867 oc_c30_0868 oc_c30_0869 oc_c30_0870 oc_c30_0871 oc_c30_0872 oc_c30_0873 oc_c30_0874 oc_c30_0875 oc_c30_0876 oc_c30_0877 oc_c30_0878 oc_c30_0879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
