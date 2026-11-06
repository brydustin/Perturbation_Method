theory OCX_c30_060
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0960: "oc_sub oc_b30 960"
  by (oc_eval oc_c30_0960)

lemma oc_c30_0961: "oc_sub oc_b30 961"
  by (oc_eval oc_c30_0961)

lemma oc_c30_0962: "oc_sub oc_b30 962"
  by (oc_eval oc_c30_0962)

lemma oc_c30_0963: "oc_sub oc_b30 963"
  by (oc_eval oc_c30_0963)

lemma oc_c30_0964: "oc_sub oc_b30 964"
  by (oc_eval oc_c30_0964)

lemma oc_c30_0965: "oc_sub oc_b30 965"
  by (oc_eval oc_c30_0965)

lemma oc_c30_0966: "oc_sub oc_b30 966"
  by (oc_eval oc_c30_0966)

lemma oc_c30_0967: "oc_sub oc_b30 967"
  by (oc_eval oc_c30_0967)

lemma oc_c30_0968: "oc_sub oc_b30 968"
  by (oc_eval oc_c30_0968)

lemma oc_c30_0969: "oc_sub oc_b30 969"
  by (oc_eval oc_c30_0969)

lemma oc_c30_0970: "oc_sub oc_b30 970"
  by (oc_eval oc_c30_0970)

lemma oc_c30_0971: "oc_sub oc_b30 971"
  by (oc_eval oc_c30_0971)

lemma oc_c30_0972: "oc_sub oc_b30 972"
  by (oc_eval oc_c30_0972)

lemma oc_c30_0973: "oc_sub oc_b30 973"
  by (oc_eval oc_c30_0973)

lemma oc_c30_0974: "oc_sub oc_b30 974"
  by (oc_eval oc_c30_0974)

lemma oc_c30_0975: "oc_sub oc_b30 975"
  by (oc_eval oc_c30_0975)

lemma upt_c30_060: "[960..<976] = [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]"
  by (simp add: upt_rec)

lemma sec_c30_060: "\<forall>j\<in>{16 * 60..<16 * 60 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 60..<16 * 60 + 16}"
  then have "j \<in> set [960..<976]" unfolding set_upt by simp
  then have "j \<in> set [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]" unfolding upt_c30_060 .
  then show "oc_sub oc_b30 j" using oc_c30_0960 oc_c30_0961 oc_c30_0962 oc_c30_0963 oc_c30_0964 oc_c30_0965 oc_c30_0966 oc_c30_0967 oc_c30_0968 oc_c30_0969 oc_c30_0970 oc_c30_0971 oc_c30_0972 oc_c30_0973 oc_c30_0974 oc_c30_0975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
