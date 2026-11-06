theory DCX_nc_056
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0896: "dc_sub None 896"
  by (dc_eval dc_nc_0896)

lemma dc_nc_0897: "dc_sub None 897"
  by (dc_eval dc_nc_0897)

lemma dc_nc_0898: "dc_sub None 898"
  by (dc_eval dc_nc_0898)

lemma dc_nc_0899: "dc_sub None 899"
  by (dc_eval dc_nc_0899)

lemma dc_nc_0900: "dc_sub None 900"
  by (dc_eval dc_nc_0900)

lemma dc_nc_0901: "dc_sub None 901"
  by (dc_eval dc_nc_0901)

lemma dc_nc_0902: "dc_sub None 902"
  by (dc_eval dc_nc_0902)

lemma dc_nc_0903: "dc_sub None 903"
  by (dc_eval dc_nc_0903)

lemma dc_nc_0904: "dc_sub None 904"
  by (dc_eval dc_nc_0904)

lemma dc_nc_0905: "dc_sub None 905"
  by (dc_eval dc_nc_0905)

lemma dc_nc_0906: "dc_sub None 906"
  by (dc_eval dc_nc_0906)

lemma dc_nc_0907: "dc_sub None 907"
  by (dc_eval dc_nc_0907)

lemma dc_nc_0908: "dc_sub None 908"
  by (dc_eval dc_nc_0908)

lemma dc_nc_0909: "dc_sub None 909"
  by (dc_eval dc_nc_0909)

lemma dc_nc_0910: "dc_sub None 910"
  by (dc_eval dc_nc_0910)

lemma dc_nc_0911: "dc_sub None 911"
  by (dc_eval dc_nc_0911)

lemma upt_nc_056: "[896..<912] = [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]"
  by (simp add: upt_rec)

lemma sec_nc_056: "\<forall>j\<in>{16 * 56..<16 * 56 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 56..<16 * 56 + 16}"
  then have "j \<in> set [896..<912]" unfolding set_upt by simp
  then have "j \<in> set [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]" unfolding upt_nc_056 .
  then show "dc_sub None j" using dc_nc_0896 dc_nc_0897 dc_nc_0898 dc_nc_0899 dc_nc_0900 dc_nc_0901 dc_nc_0902 dc_nc_0903 dc_nc_0904 dc_nc_0905 dc_nc_0906 dc_nc_0907 dc_nc_0908 dc_nc_0909 dc_nc_0910 dc_nc_0911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
