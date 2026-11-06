theory GDCX_nc_056
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0896: "gdc_sub None 896"
  by (gdc_eval gdc_nc_0896)

lemma gdc_nc_0897: "gdc_sub None 897"
  by (gdc_eval gdc_nc_0897)

lemma gdc_nc_0898: "gdc_sub None 898"
  by (gdc_eval gdc_nc_0898)

lemma gdc_nc_0899: "gdc_sub None 899"
  by (gdc_eval gdc_nc_0899)

lemma gdc_nc_0900: "gdc_sub None 900"
  by (gdc_eval gdc_nc_0900)

lemma gdc_nc_0901: "gdc_sub None 901"
  by (gdc_eval gdc_nc_0901)

lemma gdc_nc_0902: "gdc_sub None 902"
  by (gdc_eval gdc_nc_0902)

lemma gdc_nc_0903: "gdc_sub None 903"
  by (gdc_eval gdc_nc_0903)

lemma gdc_nc_0904: "gdc_sub None 904"
  by (gdc_eval gdc_nc_0904)

lemma gdc_nc_0905: "gdc_sub None 905"
  by (gdc_eval gdc_nc_0905)

lemma gdc_nc_0906: "gdc_sub None 906"
  by (gdc_eval gdc_nc_0906)

lemma gdc_nc_0907: "gdc_sub None 907"
  by (gdc_eval gdc_nc_0907)

lemma gdc_nc_0908: "gdc_sub None 908"
  by (gdc_eval gdc_nc_0908)

lemma gdc_nc_0909: "gdc_sub None 909"
  by (gdc_eval gdc_nc_0909)

lemma gdc_nc_0910: "gdc_sub None 910"
  by (gdc_eval gdc_nc_0910)

lemma gdc_nc_0911: "gdc_sub None 911"
  by (gdc_eval gdc_nc_0911)

lemma gupt_nc_056: "[896..<912] = [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]"
  by (simp add: upt_rec)

lemma gsec_nc_056: "\<forall>j\<in>{16 * 56..<16 * 56 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 56..<16 * 56 + 16}"
  then have "j \<in> set [896..<912]" unfolding set_upt by simp
  then have "j \<in> set [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]" unfolding gupt_nc_056 .
  then show "gdc_sub None j" using gdc_nc_0896 gdc_nc_0897 gdc_nc_0898 gdc_nc_0899 gdc_nc_0900 gdc_nc_0901 gdc_nc_0902 gdc_nc_0903 gdc_nc_0904 gdc_nc_0905 gdc_nc_0906 gdc_nc_0907 gdc_nc_0908 gdc_nc_0909 gdc_nc_0910 gdc_nc_0911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
