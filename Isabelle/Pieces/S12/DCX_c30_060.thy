theory DCX_c30_060
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0960: "dc_sub dc_b30 960"
  by (dc_eval dc_c30_0960)

lemma dc_c30_0961: "dc_sub dc_b30 961"
  by (dc_eval dc_c30_0961)

lemma dc_c30_0962: "dc_sub dc_b30 962"
  by (dc_eval dc_c30_0962)

lemma dc_c30_0963: "dc_sub dc_b30 963"
  by (dc_eval dc_c30_0963)

lemma dc_c30_0964: "dc_sub dc_b30 964"
  by (dc_eval dc_c30_0964)

lemma dc_c30_0965: "dc_sub dc_b30 965"
  by (dc_eval dc_c30_0965)

lemma dc_c30_0966: "dc_sub dc_b30 966"
  by (dc_eval dc_c30_0966)

lemma dc_c30_0967: "dc_sub dc_b30 967"
  by (dc_eval dc_c30_0967)

lemma dc_c30_0968: "dc_sub dc_b30 968"
  by (dc_eval dc_c30_0968)

lemma dc_c30_0969: "dc_sub dc_b30 969"
  by (dc_eval dc_c30_0969)

lemma dc_c30_0970: "dc_sub dc_b30 970"
  by (dc_eval dc_c30_0970)

lemma dc_c30_0971: "dc_sub dc_b30 971"
  by (dc_eval dc_c30_0971)

lemma dc_c30_0972: "dc_sub dc_b30 972"
  by (dc_eval dc_c30_0972)

lemma dc_c30_0973: "dc_sub dc_b30 973"
  by (dc_eval dc_c30_0973)

lemma dc_c30_0974: "dc_sub dc_b30 974"
  by (dc_eval dc_c30_0974)

lemma dc_c30_0975: "dc_sub dc_b30 975"
  by (dc_eval dc_c30_0975)

lemma upt_c30_060: "[960..<976] = [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]"
  by (simp add: upt_rec)

lemma sec_c30_060: "\<forall>j\<in>{16 * 60..<16 * 60 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 60..<16 * 60 + 16}"
  then have "j \<in> set [960..<976]" unfolding set_upt by simp
  then have "j \<in> set [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]" unfolding upt_c30_060 .
  then show "dc_sub dc_b30 j" using dc_c30_0960 dc_c30_0961 dc_c30_0962 dc_c30_0963 dc_c30_0964 dc_c30_0965 dc_c30_0966 dc_c30_0967 dc_c30_0968 dc_c30_0969 dc_c30_0970 dc_c30_0971 dc_c30_0972 dc_c30_0973 dc_c30_0974 dc_c30_0975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
