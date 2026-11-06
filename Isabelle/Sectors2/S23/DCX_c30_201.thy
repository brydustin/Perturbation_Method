theory DCX_c30_201
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3216: "dc_sub dc_b30 3216"
  by (dc_eval dc_c30_3216)

lemma dc_c30_3217: "dc_sub dc_b30 3217"
  by (dc_eval dc_c30_3217)

lemma dc_c30_3218: "dc_sub dc_b30 3218"
  by (dc_eval dc_c30_3218)

lemma dc_c30_3219: "dc_sub dc_b30 3219"
  by (dc_eval dc_c30_3219)

lemma dc_c30_3220: "dc_sub dc_b30 3220"
  by (dc_eval dc_c30_3220)

lemma dc_c30_3221: "dc_sub dc_b30 3221"
  by (dc_eval dc_c30_3221)

lemma dc_c30_3222: "dc_sub dc_b30 3222"
  by (dc_eval dc_c30_3222)

lemma dc_c30_3223: "dc_sub dc_b30 3223"
  by (dc_eval dc_c30_3223)

lemma dc_c30_3224: "dc_sub dc_b30 3224"
  by (dc_eval dc_c30_3224)

lemma dc_c30_3225: "dc_sub dc_b30 3225"
  by (dc_eval dc_c30_3225)

lemma dc_c30_3226: "dc_sub dc_b30 3226"
  by (dc_eval dc_c30_3226)

lemma dc_c30_3227: "dc_sub dc_b30 3227"
  by (dc_eval dc_c30_3227)

lemma dc_c30_3228: "dc_sub dc_b30 3228"
  by (dc_eval dc_c30_3228)

lemma dc_c30_3229: "dc_sub dc_b30 3229"
  by (dc_eval dc_c30_3229)

lemma dc_c30_3230: "dc_sub dc_b30 3230"
  by (dc_eval dc_c30_3230)

lemma dc_c30_3231: "dc_sub dc_b30 3231"
  by (dc_eval dc_c30_3231)

lemma upt_c30_201: "[3216..<3232] = [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]"
  by (simp add: upt_rec)

lemma sec_c30_201: "\<forall>j\<in>{16 * 201..<16 * 201 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 201..<16 * 201 + 16}"
  then have "j \<in> set [3216..<3232]" unfolding set_upt by simp
  then have "j \<in> set [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]" unfolding upt_c30_201 .
  then show "dc_sub dc_b30 j" using dc_c30_3216 dc_c30_3217 dc_c30_3218 dc_c30_3219 dc_c30_3220 dc_c30_3221 dc_c30_3222 dc_c30_3223 dc_c30_3224 dc_c30_3225 dc_c30_3226 dc_c30_3227 dc_c30_3228 dc_c30_3229 dc_c30_3230 dc_c30_3231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
