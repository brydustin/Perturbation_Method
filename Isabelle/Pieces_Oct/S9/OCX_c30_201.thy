theory OCX_c30_201
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3216: "oc_sub oc_b30 3216"
  by (oc_eval oc_c30_3216)

lemma oc_c30_3217: "oc_sub oc_b30 3217"
  by (oc_eval oc_c30_3217)

lemma oc_c30_3218: "oc_sub oc_b30 3218"
  by (oc_eval oc_c30_3218)

lemma oc_c30_3219: "oc_sub oc_b30 3219"
  by (oc_eval oc_c30_3219)

lemma oc_c30_3220: "oc_sub oc_b30 3220"
  by (oc_eval oc_c30_3220)

lemma oc_c30_3221: "oc_sub oc_b30 3221"
  by (oc_eval oc_c30_3221)

lemma oc_c30_3222: "oc_sub oc_b30 3222"
  by (oc_eval oc_c30_3222)

lemma oc_c30_3223: "oc_sub oc_b30 3223"
  by (oc_eval oc_c30_3223)

lemma oc_c30_3224: "oc_sub oc_b30 3224"
  by (oc_eval oc_c30_3224)

lemma oc_c30_3225: "oc_sub oc_b30 3225"
  by (oc_eval oc_c30_3225)

lemma oc_c30_3226: "oc_sub oc_b30 3226"
  by (oc_eval oc_c30_3226)

lemma oc_c30_3227: "oc_sub oc_b30 3227"
  by (oc_eval oc_c30_3227)

lemma oc_c30_3228: "oc_sub oc_b30 3228"
  by (oc_eval oc_c30_3228)

lemma oc_c30_3229: "oc_sub oc_b30 3229"
  by (oc_eval oc_c30_3229)

lemma oc_c30_3230: "oc_sub oc_b30 3230"
  by (oc_eval oc_c30_3230)

lemma oc_c30_3231: "oc_sub oc_b30 3231"
  by (oc_eval oc_c30_3231)

lemma upt_c30_201: "[3216..<3232] = [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]"
  by (simp add: upt_rec)

lemma sec_c30_201: "\<forall>j\<in>{16 * 201..<16 * 201 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 201..<16 * 201 + 16}"
  then have "j \<in> set [3216..<3232]" unfolding set_upt by simp
  then have "j \<in> set [3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]" unfolding upt_c30_201 .
  then show "oc_sub oc_b30 j" using oc_c30_3216 oc_c30_3217 oc_c30_3218 oc_c30_3219 oc_c30_3220 oc_c30_3221 oc_c30_3222 oc_c30_3223 oc_c30_3224 oc_c30_3225 oc_c30_3226 oc_c30_3227 oc_c30_3228 oc_c30_3229 oc_c30_3230 oc_c30_3231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
