theory OCX_nc_076
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1216: "oc_sub None 1216"
  by (oc_eval oc_nc_1216)

lemma oc_nc_1217: "oc_sub None 1217"
  by (oc_eval oc_nc_1217)

lemma oc_nc_1218: "oc_sub None 1218"
  by (oc_eval oc_nc_1218)

lemma oc_nc_1219: "oc_sub None 1219"
  by (oc_eval oc_nc_1219)

lemma oc_nc_1220: "oc_sub None 1220"
  by (oc_eval oc_nc_1220)

lemma oc_nc_1221: "oc_sub None 1221"
  by (oc_eval oc_nc_1221)

lemma oc_nc_1222: "oc_sub None 1222"
  by (oc_eval oc_nc_1222)

lemma oc_nc_1223: "oc_sub None 1223"
  by (oc_eval oc_nc_1223)

lemma oc_nc_1224: "oc_sub None 1224"
  by (oc_eval oc_nc_1224)

lemma oc_nc_1225: "oc_sub None 1225"
  by (oc_eval oc_nc_1225)

lemma oc_nc_1226: "oc_sub None 1226"
  by (oc_eval oc_nc_1226)

lemma oc_nc_1227: "oc_sub None 1227"
  by (oc_eval oc_nc_1227)

lemma oc_nc_1228: "oc_sub None 1228"
  by (oc_eval oc_nc_1228)

lemma oc_nc_1229: "oc_sub None 1229"
  by (oc_eval oc_nc_1229)

lemma oc_nc_1230: "oc_sub None 1230"
  by (oc_eval oc_nc_1230)

lemma oc_nc_1231: "oc_sub None 1231"
  by (oc_eval oc_nc_1231)

lemma upt_nc_076: "[1216..<1232] = [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]"
  by (simp add: upt_rec)

lemma sec_nc_076: "\<forall>j\<in>{16 * 76..<16 * 76 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 76..<16 * 76 + 16}"
  then have "j \<in> set [1216..<1232]" unfolding set_upt by simp
  then have "j \<in> set [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]" unfolding upt_nc_076 .
  then show "oc_sub None j" using oc_nc_1216 oc_nc_1217 oc_nc_1218 oc_nc_1219 oc_nc_1220 oc_nc_1221 oc_nc_1222 oc_nc_1223 oc_nc_1224 oc_nc_1225 oc_nc_1226 oc_nc_1227 oc_nc_1228 oc_nc_1229 oc_nc_1230 oc_nc_1231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
