theory OCX_c30_056
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0896: "oc_sub oc_b30 896"
  by (oc_eval oc_c30_0896)

lemma oc_c30_0897: "oc_sub oc_b30 897"
  by (oc_eval oc_c30_0897)

lemma oc_c30_0898: "oc_sub oc_b30 898"
  by (oc_eval oc_c30_0898)

lemma oc_c30_0899: "oc_sub oc_b30 899"
  by (oc_eval oc_c30_0899)

lemma oc_c30_0900: "oc_sub oc_b30 900"
  by (oc_eval oc_c30_0900)

lemma oc_c30_0901: "oc_sub oc_b30 901"
  by (oc_eval oc_c30_0901)

lemma oc_c30_0902: "oc_sub oc_b30 902"
  by (oc_eval oc_c30_0902)

lemma oc_c30_0903: "oc_sub oc_b30 903"
  by (oc_eval oc_c30_0903)

lemma oc_c30_0904: "oc_sub oc_b30 904"
  by (oc_eval oc_c30_0904)

lemma oc_c30_0905: "oc_sub oc_b30 905"
  by (oc_eval oc_c30_0905)

lemma oc_c30_0906: "oc_sub oc_b30 906"
  by (oc_eval oc_c30_0906)

lemma oc_c30_0907: "oc_sub oc_b30 907"
  by (oc_eval oc_c30_0907)

lemma oc_c30_0908: "oc_sub oc_b30 908"
  by (oc_eval oc_c30_0908)

lemma oc_c30_0909: "oc_sub oc_b30 909"
  by (oc_eval oc_c30_0909)

lemma oc_c30_0910: "oc_sub oc_b30 910"
  by (oc_eval oc_c30_0910)

lemma oc_c30_0911: "oc_sub oc_b30 911"
  by (oc_eval oc_c30_0911)

lemma upt_c30_056: "[896..<912] = [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]"
  by (simp add: upt_rec)

lemma sec_c30_056: "\<forall>j\<in>{16 * 56..<16 * 56 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 56..<16 * 56 + 16}"
  then have "j \<in> set [896..<912]" unfolding set_upt by simp
  then have "j \<in> set [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]" unfolding upt_c30_056 .
  then show "oc_sub oc_b30 j" using oc_c30_0896 oc_c30_0897 oc_c30_0898 oc_c30_0899 oc_c30_0900 oc_c30_0901 oc_c30_0902 oc_c30_0903 oc_c30_0904 oc_c30_0905 oc_c30_0906 oc_c30_0907 oc_c30_0908 oc_c30_0909 oc_c30_0910 oc_c30_0911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
