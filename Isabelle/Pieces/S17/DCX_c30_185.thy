theory DCX_c30_185
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2960: "dc_sub dc_b30 2960"
  by (dc_eval dc_c30_2960)

lemma dc_c30_2961: "dc_sub dc_b30 2961"
  by (dc_eval dc_c30_2961)

lemma dc_c30_2962: "dc_sub dc_b30 2962"
  by (dc_eval dc_c30_2962)

lemma dc_c30_2963: "dc_sub dc_b30 2963"
  by (dc_eval dc_c30_2963)

lemma dc_c30_2964: "dc_sub dc_b30 2964"
  by (dc_eval dc_c30_2964)

lemma dc_c30_2965: "dc_sub dc_b30 2965"
  by (dc_eval dc_c30_2965)

lemma dc_c30_2966: "dc_sub dc_b30 2966"
  by (dc_eval dc_c30_2966)

lemma dc_c30_2967: "dc_sub dc_b30 2967"
  by (dc_eval dc_c30_2967)

lemma dc_c30_2968: "dc_sub dc_b30 2968"
  by (dc_eval dc_c30_2968)

lemma dc_c30_2969: "dc_sub dc_b30 2969"
  by (dc_eval dc_c30_2969)

lemma dc_c30_2970: "dc_sub dc_b30 2970"
  by (dc_eval dc_c30_2970)

lemma dc_c30_2971: "dc_sub dc_b30 2971"
  by (dc_eval dc_c30_2971)

lemma dc_c30_2972: "dc_sub dc_b30 2972"
  by (dc_eval dc_c30_2972)

lemma dc_c30_2973: "dc_sub dc_b30 2973"
  by (dc_eval dc_c30_2973)

lemma dc_c30_2974: "dc_sub dc_b30 2974"
  by (dc_eval dc_c30_2974)

lemma dc_c30_2975: "dc_sub dc_b30 2975"
  by (dc_eval dc_c30_2975)

lemma upt_c30_185: "[2960..<2976] = [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]"
  by (simp add: upt_rec)

lemma sec_c30_185: "\<forall>j\<in>{16 * 185..<16 * 185 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 185..<16 * 185 + 16}"
  then have "j \<in> set [2960..<2976]" unfolding set_upt by simp
  then have "j \<in> set [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]" unfolding upt_c30_185 .
  then show "dc_sub dc_b30 j" using dc_c30_2960 dc_c30_2961 dc_c30_2962 dc_c30_2963 dc_c30_2964 dc_c30_2965 dc_c30_2966 dc_c30_2967 dc_c30_2968 dc_c30_2969 dc_c30_2970 dc_c30_2971 dc_c30_2972 dc_c30_2973 dc_c30_2974 dc_c30_2975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
