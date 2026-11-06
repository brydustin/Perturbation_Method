theory GOCX_nc_060
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0960: "goc_sub None 960"
  by (goc_eval goc_nc_0960)

lemma goc_nc_0961: "goc_sub None 961"
  by (goc_eval goc_nc_0961)

lemma goc_nc_0962: "goc_sub None 962"
  by (goc_eval goc_nc_0962)

lemma goc_nc_0963: "goc_sub None 963"
  by (goc_eval goc_nc_0963)

lemma goc_nc_0964: "goc_sub None 964"
  by (goc_eval goc_nc_0964)

lemma goc_nc_0965: "goc_sub None 965"
  by (goc_eval goc_nc_0965)

lemma goc_nc_0966: "goc_sub None 966"
  by (goc_eval goc_nc_0966)

lemma goc_nc_0967: "goc_sub None 967"
  by (goc_eval goc_nc_0967)

lemma goc_nc_0968: "goc_sub None 968"
  by (goc_eval goc_nc_0968)

lemma goc_nc_0969: "goc_sub None 969"
  by (goc_eval goc_nc_0969)

lemma goc_nc_0970: "goc_sub None 970"
  by (goc_eval goc_nc_0970)

lemma goc_nc_0971: "goc_sub None 971"
  by (goc_eval goc_nc_0971)

lemma goc_nc_0972: "goc_sub None 972"
  by (goc_eval goc_nc_0972)

lemma goc_nc_0973: "goc_sub None 973"
  by (goc_eval goc_nc_0973)

lemma goc_nc_0974: "goc_sub None 974"
  by (goc_eval goc_nc_0974)

lemma goc_nc_0975: "goc_sub None 975"
  by (goc_eval goc_nc_0975)

lemma gupt_nc_060: "[960..<976] = [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]"
  by (simp add: upt_rec)

lemma gsec_nc_060: "\<forall>j\<in>{16 * 60..<16 * 60 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 60..<16 * 60 + 16}"
  then have "j \<in> set [960..<976]" unfolding set_upt by simp
  then have "j \<in> set [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]" unfolding gupt_nc_060 .
  then show "goc_sub None j" using goc_nc_0960 goc_nc_0961 goc_nc_0962 goc_nc_0963 goc_nc_0964 goc_nc_0965 goc_nc_0966 goc_nc_0967 goc_nc_0968 goc_nc_0969 goc_nc_0970 goc_nc_0971 goc_nc_0972 goc_nc_0973 goc_nc_0974 goc_nc_0975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
