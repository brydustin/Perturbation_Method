theory OCX_nc_056
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0896: "oc_sub None 896"
  by (oc_eval oc_nc_0896)

lemma oc_nc_0897: "oc_sub None 897"
  by (oc_eval oc_nc_0897)

lemma oc_nc_0898: "oc_sub None 898"
  by (oc_eval oc_nc_0898)

lemma oc_nc_0899: "oc_sub None 899"
  by (oc_eval oc_nc_0899)

lemma oc_nc_0900: "oc_sub None 900"
  by (oc_eval oc_nc_0900)

lemma oc_nc_0901: "oc_sub None 901"
  by (oc_eval oc_nc_0901)

lemma oc_nc_0902: "oc_sub None 902"
  by (oc_eval oc_nc_0902)

lemma oc_nc_0903: "oc_sub None 903"
  by (oc_eval oc_nc_0903)

lemma oc_nc_0904: "oc_sub None 904"
  by (oc_eval oc_nc_0904)

lemma oc_nc_0905: "oc_sub None 905"
  by (oc_eval oc_nc_0905)

lemma oc_nc_0906: "oc_sub None 906"
  by (oc_eval oc_nc_0906)

lemma oc_nc_0907: "oc_sub None 907"
  by (oc_eval oc_nc_0907)

lemma oc_nc_0908: "oc_sub None 908"
  by (oc_eval oc_nc_0908)

lemma oc_nc_0909: "oc_sub None 909"
  by (oc_eval oc_nc_0909)

lemma oc_nc_0910: "oc_sub None 910"
  by (oc_eval oc_nc_0910)

lemma oc_nc_0911: "oc_sub None 911"
  by (oc_eval oc_nc_0911)

lemma upt_nc_056: "[896..<912] = [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]"
  by (simp add: upt_rec)

lemma sec_nc_056: "\<forall>j\<in>{16 * 56..<16 * 56 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 56..<16 * 56 + 16}"
  then have "j \<in> set [896..<912]" unfolding set_upt by simp
  then have "j \<in> set [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]" unfolding upt_nc_056 .
  then show "oc_sub None j" using oc_nc_0896 oc_nc_0897 oc_nc_0898 oc_nc_0899 oc_nc_0900 oc_nc_0901 oc_nc_0902 oc_nc_0903 oc_nc_0904 oc_nc_0905 oc_nc_0906 oc_nc_0907 oc_nc_0908 oc_nc_0909 oc_nc_0910 oc_nc_0911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
