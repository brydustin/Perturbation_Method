theory GDCX_nc_185
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2960: "gdc_sub None 2960"
  by (gdc_eval gdc_nc_2960)

lemma gdc_nc_2961: "gdc_sub None 2961"
  by (gdc_eval gdc_nc_2961)

lemma gdc_nc_2962: "gdc_sub None 2962"
  by (gdc_eval gdc_nc_2962)

lemma gdc_nc_2963: "gdc_sub None 2963"
  by (gdc_eval gdc_nc_2963)

lemma gdc_nc_2964: "gdc_sub None 2964"
  by (gdc_eval gdc_nc_2964)

lemma gdc_nc_2965: "gdc_sub None 2965"
  by (gdc_eval gdc_nc_2965)

lemma gdc_nc_2966: "gdc_sub None 2966"
  by (gdc_eval gdc_nc_2966)

lemma gdc_nc_2967: "gdc_sub None 2967"
  by (gdc_eval gdc_nc_2967)

lemma gdc_nc_2968: "gdc_sub None 2968"
  by (gdc_eval gdc_nc_2968)

lemma gdc_nc_2969: "gdc_sub None 2969"
  by (gdc_eval gdc_nc_2969)

lemma gdc_nc_2970: "gdc_sub None 2970"
  by (gdc_eval gdc_nc_2970)

lemma gdc_nc_2971: "gdc_sub None 2971"
  by (gdc_eval gdc_nc_2971)

lemma gdc_nc_2972: "gdc_sub None 2972"
  by (gdc_eval gdc_nc_2972)

lemma gdc_nc_2973: "gdc_sub None 2973"
  by (gdc_eval gdc_nc_2973)

lemma gdc_nc_2974: "gdc_sub None 2974"
  by (gdc_eval gdc_nc_2974)

lemma gdc_nc_2975: "gdc_sub None 2975"
  by (gdc_eval gdc_nc_2975)

lemma gupt_nc_185: "[2960..<2976] = [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]"
  by (simp add: upt_rec)

lemma gsec_nc_185: "\<forall>j\<in>{16 * 185..<16 * 185 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 185..<16 * 185 + 16}"
  then have "j \<in> set [2960..<2976]" unfolding set_upt by simp
  then have "j \<in> set [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]" unfolding gupt_nc_185 .
  then show "gdc_sub None j" using gdc_nc_2960 gdc_nc_2961 gdc_nc_2962 gdc_nc_2963 gdc_nc_2964 gdc_nc_2965 gdc_nc_2966 gdc_nc_2967 gdc_nc_2968 gdc_nc_2969 gdc_nc_2970 gdc_nc_2971 gdc_nc_2972 gdc_nc_2973 gdc_nc_2974 gdc_nc_2975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
