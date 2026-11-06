theory GOCX_nc_201
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3216: "goc_sub None 3216"
  by (goc_eval goc_nc_3216)

lemma goc_nc_3217: "goc_sub None 3217"
  by (goc_eval goc_nc_3217)

lemma goc_nc_3218: "goc_sub None 3218"
  by (goc_eval goc_nc_3218)

lemma goc_nc_3219: "goc_sub None 3219"
  by (goc_eval goc_nc_3219)

lemma goc_nc_3220: "goc_sub None 3220"
  by (goc_eval goc_nc_3220)

lemma goc_nc_3221: "goc_sub None 3221"
  by (goc_eval goc_nc_3221)

lemma goc_nc_3222: "goc_sub None 3222"
  by (goc_eval goc_nc_3222)

lemma goc_nc_3223: "goc_sub None 3223"
  by (goc_eval goc_nc_3223)

lemma goc_nc_3224: "goc_sub None 3224"
  by (goc_eval goc_nc_3224)

lemma goc_nc_3225: "goc_sub None 3225"
  by (goc_eval goc_nc_3225)

lemma goc_nc_3226: "goc_sub None 3226"
  by (goc_eval goc_nc_3226)

lemma goc_nc_3227: "goc_sub None 3227"
  by (goc_eval goc_nc_3227)

lemma goc_nc_3228: "goc_sub None 3228"
  by (goc_eval goc_nc_3228)

lemma goc_nc_3229: "goc_sub None 3229"
  by (goc_eval goc_nc_3229)

lemma goc_nc_3230: "goc_sub None 3230"
  by (goc_eval goc_nc_3230)

lemma goc_nc_3231: "goc_sub None 3231"
  by (goc_eval goc_nc_3231)

lemma gupt_nc_201: "[3216..<3232] = [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]"
  by (simp add: upt_rec)

lemma gsec_nc_201: "\<forall>j\<in>{16 * 201..<16 * 201 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 201..<16 * 201 + 16}"
  then have "j \<in> set [3216..<3232]" unfolding set_upt by simp
  then have "j \<in> set [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]" unfolding gupt_nc_201 .
  then show "goc_sub None j" using goc_nc_3216 goc_nc_3217 goc_nc_3218 goc_nc_3219 goc_nc_3220 goc_nc_3221 goc_nc_3222 goc_nc_3223 goc_nc_3224 goc_nc_3225 goc_nc_3226 goc_nc_3227 goc_nc_3228 goc_nc_3229 goc_nc_3230 goc_nc_3231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
