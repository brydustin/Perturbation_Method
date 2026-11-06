theory OCX_nc_060
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0960: "oc_sub None 960"
  by (oc_eval oc_nc_0960)

lemma oc_nc_0961: "oc_sub None 961"
  by (oc_eval oc_nc_0961)

lemma oc_nc_0962: "oc_sub None 962"
  by (oc_eval oc_nc_0962)

lemma oc_nc_0963: "oc_sub None 963"
  by (oc_eval oc_nc_0963)

lemma oc_nc_0964: "oc_sub None 964"
  by (oc_eval oc_nc_0964)

lemma oc_nc_0965: "oc_sub None 965"
  by (oc_eval oc_nc_0965)

lemma oc_nc_0966: "oc_sub None 966"
  by (oc_eval oc_nc_0966)

lemma oc_nc_0967: "oc_sub None 967"
  by (oc_eval oc_nc_0967)

lemma oc_nc_0968: "oc_sub None 968"
  by (oc_eval oc_nc_0968)

lemma oc_nc_0969: "oc_sub None 969"
  by (oc_eval oc_nc_0969)

lemma oc_nc_0970: "oc_sub None 970"
  by (oc_eval oc_nc_0970)

lemma oc_nc_0971: "oc_sub None 971"
  by (oc_eval oc_nc_0971)

lemma oc_nc_0972: "oc_sub None 972"
  by (oc_eval oc_nc_0972)

lemma oc_nc_0973: "oc_sub None 973"
  by (oc_eval oc_nc_0973)

lemma oc_nc_0974: "oc_sub None 974"
  by (oc_eval oc_nc_0974)

lemma oc_nc_0975: "oc_sub None 975"
  by (oc_eval oc_nc_0975)

lemma upt_nc_060: "[960..<976] = [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]"
  by (simp add: upt_rec)

lemma sec_nc_060: "\<forall>j\<in>{16 * 60..<16 * 60 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 60..<16 * 60 + 16}"
  then have "j \<in> set [960..<976]" unfolding set_upt by simp
  then have "j \<in> set [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]" unfolding upt_nc_060 .
  then show "oc_sub None j" using oc_nc_0960 oc_nc_0961 oc_nc_0962 oc_nc_0963 oc_nc_0964 oc_nc_0965 oc_nc_0966 oc_nc_0967 oc_nc_0968 oc_nc_0969 oc_nc_0970 oc_nc_0971 oc_nc_0972 oc_nc_0973 oc_nc_0974 oc_nc_0975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
