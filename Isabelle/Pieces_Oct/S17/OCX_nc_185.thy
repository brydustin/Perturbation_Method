theory OCX_nc_185
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2960: "oc_sub None 2960"
  by (oc_eval oc_nc_2960)

lemma oc_nc_2961: "oc_sub None 2961"
  by (oc_eval oc_nc_2961)

lemma oc_nc_2962: "oc_sub None 2962"
  by (oc_eval oc_nc_2962)

lemma oc_nc_2963: "oc_sub None 2963"
  by (oc_eval oc_nc_2963)

lemma oc_nc_2964: "oc_sub None 2964"
  by (oc_eval oc_nc_2964)

lemma oc_nc_2965: "oc_sub None 2965"
  by (oc_eval oc_nc_2965)

lemma oc_nc_2966: "oc_sub None 2966"
  by (oc_eval oc_nc_2966)

lemma oc_nc_2967: "oc_sub None 2967"
  by (oc_eval oc_nc_2967)

lemma oc_nc_2968: "oc_sub None 2968"
  by (oc_eval oc_nc_2968)

lemma oc_nc_2969: "oc_sub None 2969"
  by (oc_eval oc_nc_2969)

lemma oc_nc_2970: "oc_sub None 2970"
  by (oc_eval oc_nc_2970)

lemma oc_nc_2971: "oc_sub None 2971"
  by (oc_eval oc_nc_2971)

lemma oc_nc_2972: "oc_sub None 2972"
  by (oc_eval oc_nc_2972)

lemma oc_nc_2973: "oc_sub None 2973"
  by (oc_eval oc_nc_2973)

lemma oc_nc_2974: "oc_sub None 2974"
  by (oc_eval oc_nc_2974)

lemma oc_nc_2975: "oc_sub None 2975"
  by (oc_eval oc_nc_2975)

lemma upt_nc_185: "[2960..<2976] = [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]"
  by (simp add: upt_rec)

lemma sec_nc_185: "\<forall>j\<in>{16 * 185..<16 * 185 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 185..<16 * 185 + 16}"
  then have "j \<in> set [2960..<2976]" unfolding set_upt by simp
  then have "j \<in> set [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]" unfolding upt_nc_185 .
  then show "oc_sub None j" using oc_nc_2960 oc_nc_2961 oc_nc_2962 oc_nc_2963 oc_nc_2964 oc_nc_2965 oc_nc_2966 oc_nc_2967 oc_nc_2968 oc_nc_2969 oc_nc_2970 oc_nc_2971 oc_nc_2972 oc_nc_2973 oc_nc_2974 oc_nc_2975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
