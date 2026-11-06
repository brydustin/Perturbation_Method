theory DCX_c30_076
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1216: "dc_sub dc_b30 1216"
  by (dc_eval dc_c30_1216)

lemma dc_c30_1217: "dc_sub dc_b30 1217"
  by (dc_eval dc_c30_1217)

lemma dc_c30_1218: "dc_sub dc_b30 1218"
  by (dc_eval dc_c30_1218)

lemma dc_c30_1219: "dc_sub dc_b30 1219"
  by (dc_eval dc_c30_1219)

lemma dc_c30_1220: "dc_sub dc_b30 1220"
  by (dc_eval dc_c30_1220)

lemma dc_c30_1221: "dc_sub dc_b30 1221"
  by (dc_eval dc_c30_1221)

lemma dc_c30_1222: "dc_sub dc_b30 1222"
  by (dc_eval dc_c30_1222)

lemma dc_c30_1223: "dc_sub dc_b30 1223"
  by (dc_eval dc_c30_1223)

lemma dc_c30_1224: "dc_sub dc_b30 1224"
  by (dc_eval dc_c30_1224)

lemma dc_c30_1225: "dc_sub dc_b30 1225"
  by (dc_eval dc_c30_1225)

lemma dc_c30_1226: "dc_sub dc_b30 1226"
  by (dc_eval dc_c30_1226)

lemma dc_c30_1227: "dc_sub dc_b30 1227"
  by (dc_eval dc_c30_1227)

lemma dc_c30_1228: "dc_sub dc_b30 1228"
  by (dc_eval dc_c30_1228)

lemma dc_c30_1229: "dc_sub dc_b30 1229"
  by (dc_eval dc_c30_1229)

lemma dc_c30_1230: "dc_sub dc_b30 1230"
  by (dc_eval dc_c30_1230)

lemma dc_c30_1231: "dc_sub dc_b30 1231"
  by (dc_eval dc_c30_1231)

lemma upt_c30_076: "[1216..<1232] = [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]"
  by (simp add: upt_rec)

lemma sec_c30_076: "\<forall>j\<in>{16 * 76..<16 * 76 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 76..<16 * 76 + 16}"
  then have "j \<in> set [1216..<1232]" unfolding set_upt by simp
  then have "j \<in> set [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]" unfolding upt_c30_076 .
  then show "dc_sub dc_b30 j" using dc_c30_1216 dc_c30_1217 dc_c30_1218 dc_c30_1219 dc_c30_1220 dc_c30_1221 dc_c30_1222 dc_c30_1223 dc_c30_1224 dc_c30_1225 dc_c30_1226 dc_c30_1227 dc_c30_1228 dc_c30_1229 dc_c30_1230 dc_c30_1231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
