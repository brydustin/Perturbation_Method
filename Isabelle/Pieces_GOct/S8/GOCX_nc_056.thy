theory GOCX_nc_056
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0896: "goc_sub None 896"
  by (goc_eval goc_nc_0896)

lemma goc_nc_0897: "goc_sub None 897"
  by (goc_eval goc_nc_0897)

lemma goc_nc_0898: "goc_sub None 898"
  by (goc_eval goc_nc_0898)

lemma goc_nc_0899: "goc_sub None 899"
  by (goc_eval goc_nc_0899)

lemma goc_nc_0900: "goc_sub None 900"
  by (goc_eval goc_nc_0900)

lemma goc_nc_0901: "goc_sub None 901"
  by (goc_eval goc_nc_0901)

lemma goc_nc_0902: "goc_sub None 902"
  by (goc_eval goc_nc_0902)

lemma goc_nc_0903: "goc_sub None 903"
  by (goc_eval goc_nc_0903)

lemma goc_nc_0904: "goc_sub None 904"
  by (goc_eval goc_nc_0904)

lemma goc_nc_0905: "goc_sub None 905"
  by (goc_eval goc_nc_0905)

lemma goc_nc_0906: "goc_sub None 906"
  by (goc_eval goc_nc_0906)

lemma goc_nc_0907: "goc_sub None 907"
  by (goc_eval goc_nc_0907)

lemma goc_nc_0908: "goc_sub None 908"
  by (goc_eval goc_nc_0908)

lemma goc_nc_0909: "goc_sub None 909"
  by (goc_eval goc_nc_0909)

lemma goc_nc_0910: "goc_sub None 910"
  by (goc_eval goc_nc_0910)

lemma goc_nc_0911: "goc_sub None 911"
  by (goc_eval goc_nc_0911)

lemma gupt_nc_056: "[896..<912] = [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]"
  by (simp add: upt_rec)

lemma gsec_nc_056: "\<forall>j\<in>{16 * 56..<16 * 56 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 56..<16 * 56 + 16}"
  then have "j \<in> set [896..<912]" unfolding set_upt by simp
  then have "j \<in> set [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]" unfolding gupt_nc_056 .
  then show "goc_sub None j" using goc_nc_0896 goc_nc_0897 goc_nc_0898 goc_nc_0899 goc_nc_0900 goc_nc_0901 goc_nc_0902 goc_nc_0903 goc_nc_0904 goc_nc_0905 goc_nc_0906 goc_nc_0907 goc_nc_0908 goc_nc_0909 goc_nc_0910 goc_nc_0911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
