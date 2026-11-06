theory DCX_nc_060
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0960: "dc_sub None 960"
  by (dc_eval dc_nc_0960)

lemma dc_nc_0961: "dc_sub None 961"
  by (dc_eval dc_nc_0961)

lemma dc_nc_0962: "dc_sub None 962"
  by (dc_eval dc_nc_0962)

lemma dc_nc_0963: "dc_sub None 963"
  by (dc_eval dc_nc_0963)

lemma dc_nc_0964: "dc_sub None 964"
  by (dc_eval dc_nc_0964)

lemma dc_nc_0965: "dc_sub None 965"
  by (dc_eval dc_nc_0965)

lemma dc_nc_0966: "dc_sub None 966"
  by (dc_eval dc_nc_0966)

lemma dc_nc_0967: "dc_sub None 967"
  by (dc_eval dc_nc_0967)

lemma dc_nc_0968: "dc_sub None 968"
  by (dc_eval dc_nc_0968)

lemma dc_nc_0969: "dc_sub None 969"
  by (dc_eval dc_nc_0969)

lemma dc_nc_0970: "dc_sub None 970"
  by (dc_eval dc_nc_0970)

lemma dc_nc_0971: "dc_sub None 971"
  by (dc_eval dc_nc_0971)

lemma dc_nc_0972: "dc_sub None 972"
  by (dc_eval dc_nc_0972)

lemma dc_nc_0973: "dc_sub None 973"
  by (dc_eval dc_nc_0973)

lemma dc_nc_0974: "dc_sub None 974"
  by (dc_eval dc_nc_0974)

lemma dc_nc_0975: "dc_sub None 975"
  by (dc_eval dc_nc_0975)

lemma upt_nc_060: "[960..<976] = [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]"
  by (simp add: upt_rec)

lemma sec_nc_060: "\<forall>j\<in>{16 * 60..<16 * 60 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 60..<16 * 60 + 16}"
  then have "j \<in> set [960..<976]" unfolding set_upt by simp
  then have "j \<in> set [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]" unfolding upt_nc_060 .
  then show "dc_sub None j" using dc_nc_0960 dc_nc_0961 dc_nc_0962 dc_nc_0963 dc_nc_0964 dc_nc_0965 dc_nc_0966 dc_nc_0967 dc_nc_0968 dc_nc_0969 dc_nc_0970 dc_nc_0971 dc_nc_0972 dc_nc_0973 dc_nc_0974 dc_nc_0975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
