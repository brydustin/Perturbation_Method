theory DCX_c30_056
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0896: "dc_sub dc_b30 896"
  by (dc_eval dc_c30_0896)

lemma dc_c30_0897: "dc_sub dc_b30 897"
  by (dc_eval dc_c30_0897)

lemma dc_c30_0898: "dc_sub dc_b30 898"
  by (dc_eval dc_c30_0898)

lemma dc_c30_0899: "dc_sub dc_b30 899"
  by (dc_eval dc_c30_0899)

lemma dc_c30_0900: "dc_sub dc_b30 900"
  by (dc_eval dc_c30_0900)

lemma dc_c30_0901: "dc_sub dc_b30 901"
  by (dc_eval dc_c30_0901)

lemma dc_c30_0902: "dc_sub dc_b30 902"
  by (dc_eval dc_c30_0902)

lemma dc_c30_0903: "dc_sub dc_b30 903"
  by (dc_eval dc_c30_0903)

lemma dc_c30_0904: "dc_sub dc_b30 904"
  by (dc_eval dc_c30_0904)

lemma dc_c30_0905: "dc_sub dc_b30 905"
  by (dc_eval dc_c30_0905)

lemma dc_c30_0906: "dc_sub dc_b30 906"
  by (dc_eval dc_c30_0906)

lemma dc_c30_0907: "dc_sub dc_b30 907"
  by (dc_eval dc_c30_0907)

lemma dc_c30_0908: "dc_sub dc_b30 908"
  by (dc_eval dc_c30_0908)

lemma dc_c30_0909: "dc_sub dc_b30 909"
  by (dc_eval dc_c30_0909)

lemma dc_c30_0910: "dc_sub dc_b30 910"
  by (dc_eval dc_c30_0910)

lemma dc_c30_0911: "dc_sub dc_b30 911"
  by (dc_eval dc_c30_0911)

lemma upt_c30_056: "[896..<912] = [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]"
  by (simp add: upt_rec)

lemma sec_c30_056: "\<forall>j\<in>{16 * 56..<16 * 56 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 56..<16 * 56 + 16}"
  then have "j \<in> set [896..<912]" unfolding set_upt by simp
  then have "j \<in> set [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]" unfolding upt_c30_056 .
  then show "dc_sub dc_b30 j" using dc_c30_0896 dc_c30_0897 dc_c30_0898 dc_c30_0899 dc_c30_0900 dc_c30_0901 dc_c30_0902 dc_c30_0903 dc_c30_0904 dc_c30_0905 dc_c30_0906 dc_c30_0907 dc_c30_0908 dc_c30_0909 dc_c30_0910 dc_c30_0911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
