theory GDCX_nc_201
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3216: "gdc_sub None 3216"
  by (gdc_eval gdc_nc_3216)

lemma gdc_nc_3217: "gdc_sub None 3217"
  by (gdc_eval gdc_nc_3217)

lemma gdc_nc_3218: "gdc_sub None 3218"
  by (gdc_eval gdc_nc_3218)

lemma gdc_nc_3219: "gdc_sub None 3219"
  by (gdc_eval gdc_nc_3219)

lemma gdc_nc_3220: "gdc_sub None 3220"
  by (gdc_eval gdc_nc_3220)

lemma gdc_nc_3221: "gdc_sub None 3221"
  by (gdc_eval gdc_nc_3221)

lemma gdc_nc_3222: "gdc_sub None 3222"
  by (gdc_eval gdc_nc_3222)

lemma gdc_nc_3223: "gdc_sub None 3223"
  by (gdc_eval gdc_nc_3223)

lemma gdc_nc_3224: "gdc_sub None 3224"
  by (gdc_eval gdc_nc_3224)

lemma gdc_nc_3225: "gdc_sub None 3225"
  by (gdc_eval gdc_nc_3225)

lemma gdc_nc_3226: "gdc_sub None 3226"
  by (gdc_eval gdc_nc_3226)

lemma gdc_nc_3227: "gdc_sub None 3227"
  by (gdc_eval gdc_nc_3227)

lemma gdc_nc_3228: "gdc_sub None 3228"
  by (gdc_eval gdc_nc_3228)

lemma gdc_nc_3229: "gdc_sub None 3229"
  by (gdc_eval gdc_nc_3229)

lemma gdc_nc_3230: "gdc_sub None 3230"
  by (gdc_eval gdc_nc_3230)

lemma gdc_nc_3231: "gdc_sub None 3231"
  by (gdc_eval gdc_nc_3231)

lemma gupt_nc_201: "[3216..<3232] = [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]"
  by (simp add: upt_rec)

lemma gsec_nc_201: "\<forall>j\<in>{16 * 201..<16 * 201 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 201..<16 * 201 + 16}"
  then have "j \<in> set [3216..<3232]" unfolding set_upt by simp
  then have "j \<in> set [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]" unfolding gupt_nc_201 .
  then show "gdc_sub None j" using gdc_nc_3216 gdc_nc_3217 gdc_nc_3218 gdc_nc_3219 gdc_nc_3220 gdc_nc_3221 gdc_nc_3222 gdc_nc_3223 gdc_nc_3224 gdc_nc_3225 gdc_nc_3226 gdc_nc_3227 gdc_nc_3228 gdc_nc_3229 gdc_nc_3230 gdc_nc_3231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
