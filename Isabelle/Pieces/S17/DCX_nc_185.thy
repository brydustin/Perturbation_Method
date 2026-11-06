theory DCX_nc_185
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2960: "dc_sub None 2960"
  by (dc_eval dc_nc_2960)

lemma dc_nc_2961: "dc_sub None 2961"
  by (dc_eval dc_nc_2961)

lemma dc_nc_2962: "dc_sub None 2962"
  by (dc_eval dc_nc_2962)

lemma dc_nc_2963: "dc_sub None 2963"
  by (dc_eval dc_nc_2963)

lemma dc_nc_2964: "dc_sub None 2964"
  by (dc_eval dc_nc_2964)

lemma dc_nc_2965: "dc_sub None 2965"
  by (dc_eval dc_nc_2965)

lemma dc_nc_2966: "dc_sub None 2966"
  by (dc_eval dc_nc_2966)

lemma dc_nc_2967: "dc_sub None 2967"
  by (dc_eval dc_nc_2967)

lemma dc_nc_2968: "dc_sub None 2968"
  by (dc_eval dc_nc_2968)

lemma dc_nc_2969: "dc_sub None 2969"
  by (dc_eval dc_nc_2969)

lemma dc_nc_2970: "dc_sub None 2970"
  by (dc_eval dc_nc_2970)

lemma dc_nc_2971: "dc_sub None 2971"
  by (dc_eval dc_nc_2971)

lemma dc_nc_2972: "dc_sub None 2972"
  by (dc_eval dc_nc_2972)

lemma dc_nc_2973: "dc_sub None 2973"
  by (dc_eval dc_nc_2973)

lemma dc_nc_2974: "dc_sub None 2974"
  by (dc_eval dc_nc_2974)

lemma dc_nc_2975: "dc_sub None 2975"
  by (dc_eval dc_nc_2975)

lemma upt_nc_185: "[2960..<2976] = [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]"
  by (simp add: upt_rec)

lemma sec_nc_185: "\<forall>j\<in>{16 * 185..<16 * 185 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 185..<16 * 185 + 16}"
  then have "j \<in> set [2960..<2976]" unfolding set_upt by simp
  then have "j \<in> set [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]" unfolding upt_nc_185 .
  then show "dc_sub None j" using dc_nc_2960 dc_nc_2961 dc_nc_2962 dc_nc_2963 dc_nc_2964 dc_nc_2965 dc_nc_2966 dc_nc_2967 dc_nc_2968 dc_nc_2969 dc_nc_2970 dc_nc_2971 dc_nc_2972 dc_nc_2973 dc_nc_2974 dc_nc_2975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
