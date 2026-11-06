theory GOCX_nc_185
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2960: "goc_sub None 2960"
  by (goc_eval goc_nc_2960)

lemma goc_nc_2961: "goc_sub None 2961"
  by (goc_eval goc_nc_2961)

lemma goc_nc_2962: "goc_sub None 2962"
  by (goc_eval goc_nc_2962)

lemma goc_nc_2963: "goc_sub None 2963"
  by (goc_eval goc_nc_2963)

lemma goc_nc_2964: "goc_sub None 2964"
  by (goc_eval goc_nc_2964)

lemma goc_nc_2965: "goc_sub None 2965"
  by (goc_eval goc_nc_2965)

lemma goc_nc_2966: "goc_sub None 2966"
  by (goc_eval goc_nc_2966)

lemma goc_nc_2967: "goc_sub None 2967"
  by (goc_eval goc_nc_2967)

lemma goc_nc_2968: "goc_sub None 2968"
  by (goc_eval goc_nc_2968)

lemma goc_nc_2969: "goc_sub None 2969"
  by (goc_eval goc_nc_2969)

lemma goc_nc_2970: "goc_sub None 2970"
  by (goc_eval goc_nc_2970)

lemma goc_nc_2971: "goc_sub None 2971"
  by (goc_eval goc_nc_2971)

lemma goc_nc_2972: "goc_sub None 2972"
  by (goc_eval goc_nc_2972)

lemma goc_nc_2973: "goc_sub None 2973"
  by (goc_eval goc_nc_2973)

lemma goc_nc_2974: "goc_sub None 2974"
  by (goc_eval goc_nc_2974)

lemma goc_nc_2975: "goc_sub None 2975"
  by (goc_eval goc_nc_2975)

lemma gupt_nc_185: "[2960..<2976] = [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]"
  by (simp add: upt_rec)

lemma gsec_nc_185: "\<forall>j\<in>{16 * 185..<16 * 185 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 185..<16 * 185 + 16}"
  then have "j \<in> set [2960..<2976]" unfolding set_upt by simp
  then have "j \<in> set [2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]" unfolding gupt_nc_185 .
  then show "goc_sub None j" using goc_nc_2960 goc_nc_2961 goc_nc_2962 goc_nc_2963 goc_nc_2964 goc_nc_2965 goc_nc_2966 goc_nc_2967 goc_nc_2968 goc_nc_2969 goc_nc_2970 goc_nc_2971 goc_nc_2972 goc_nc_2973 goc_nc_2974 goc_nc_2975
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
