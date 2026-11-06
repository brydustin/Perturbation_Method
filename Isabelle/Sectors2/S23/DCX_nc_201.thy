theory DCX_nc_201
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3216: "dc_sub None 3216"
  by (dc_eval dc_nc_3216)

lemma dc_nc_3217: "dc_sub None 3217"
  by (dc_eval dc_nc_3217)

lemma dc_nc_3218: "dc_sub None 3218"
  by (dc_eval dc_nc_3218)

lemma dc_nc_3219: "dc_sub None 3219"
  by (dc_eval dc_nc_3219)

lemma dc_nc_3220: "dc_sub None 3220"
  by (dc_eval dc_nc_3220)

lemma dc_nc_3221: "dc_sub None 3221"
  by (dc_eval dc_nc_3221)

lemma dc_nc_3222: "dc_sub None 3222"
  by (dc_eval dc_nc_3222)

lemma dc_nc_3223: "dc_sub None 3223"
  by (dc_eval dc_nc_3223)

lemma dc_nc_3224: "dc_sub None 3224"
  by (dc_eval dc_nc_3224)

lemma dc_nc_3225: "dc_sub None 3225"
  by (dc_eval dc_nc_3225)

lemma dc_nc_3226: "dc_sub None 3226"
  by (dc_eval dc_nc_3226)

lemma dc_nc_3227: "dc_sub None 3227"
  by (dc_eval dc_nc_3227)

lemma dc_nc_3228: "dc_sub None 3228"
  by (dc_eval dc_nc_3228)

lemma dc_nc_3229: "dc_sub None 3229"
  by (dc_eval dc_nc_3229)

lemma dc_nc_3230: "dc_sub None 3230"
  by (dc_eval dc_nc_3230)

lemma dc_nc_3231: "dc_sub None 3231"
  by (dc_eval dc_nc_3231)

lemma upt_nc_201: "[3216..<3232] = [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]"
  by (simp add: upt_rec)

lemma sec_nc_201: "\<forall>j\<in>{16 * 201..<16 * 201 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 201..<16 * 201 + 16}"
  then have "j \<in> set [3216..<3232]" unfolding set_upt by simp
  then have "j \<in> set [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]" unfolding upt_nc_201 .
  then show "dc_sub None j" using dc_nc_3216 dc_nc_3217 dc_nc_3218 dc_nc_3219 dc_nc_3220 dc_nc_3221 dc_nc_3222 dc_nc_3223 dc_nc_3224 dc_nc_3225 dc_nc_3226 dc_nc_3227 dc_nc_3228 dc_nc_3229 dc_nc_3230 dc_nc_3231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
