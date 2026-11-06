theory GDCX_nc_060
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0960: "gdc_sub None 960"
  by (gdc_eval gdc_nc_0960)

lemma gdc_nc_0961: "gdc_sub None 961"
  by (gdc_eval gdc_nc_0961)

lemma gdc_nc_0962: "gdc_sub None 962"
  by (gdc_eval gdc_nc_0962)

lemma gdc_nc_0963: "gdc_sub None 963"
  by (gdc_eval gdc_nc_0963)

lemma gdc_nc_0964: "gdc_sub None 964"
  by (gdc_eval gdc_nc_0964)

lemma gdc_nc_0965: "gdc_sub None 965"
  by (gdc_eval gdc_nc_0965)

lemma gdc_nc_0966: "gdc_sub None 966"
  by (gdc_eval gdc_nc_0966)

lemma gdc_nc_0967: "gdc_sub None 967"
  by (gdc_eval gdc_nc_0967)

lemma gdc_nc_0968: "gdc_sub None 968"
  by (gdc_eval gdc_nc_0968)

lemma gdc_nc_0969: "gdc_sub None 969"
  by (gdc_eval gdc_nc_0969)

lemma gdc_nc_0970: "gdc_sub None 970"
  by (gdc_eval gdc_nc_0970)

lemma gdc_nc_0971: "gdc_sub None 971"
  by (gdc_eval gdc_nc_0971)

lemma gdc_nc_0972: "gdc_sub None 972"
  by (gdc_eval gdc_nc_0972)

lemma gdc_nc_0973: "gdc_sub None 973"
  by (gdc_eval gdc_nc_0973)

lemma gdc_nc_0974: "gdc_sub None 974"
  by (gdc_eval gdc_nc_0974)

lemma gdc_nc_0975: "gdc_sub None 975"
  by (gdc_eval gdc_nc_0975)

lemma gupt_nc_060: "[960..<976] = [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]"
  by (simp add: upt_rec)

lemma gsec_nc_060: "\<forall>j\<in>{16 * 60..<16 * 60 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 60..<16 * 60 + 16}"
  then have "j \<in> set [960..<976]" unfolding set_upt by simp
  then have "j \<in> set [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]" unfolding gupt_nc_060 .
  then show "gdc_sub None j" using gdc_nc_0960 gdc_nc_0961 gdc_nc_0962 gdc_nc_0963 gdc_nc_0964 gdc_nc_0965 gdc_nc_0966 gdc_nc_0967 gdc_nc_0968 gdc_nc_0969 gdc_nc_0970 gdc_nc_0971 gdc_nc_0972 gdc_nc_0973 gdc_nc_0974 gdc_nc_0975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
