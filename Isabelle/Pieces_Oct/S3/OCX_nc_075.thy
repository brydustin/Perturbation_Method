theory OCX_nc_075
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1200: "oc_sub None 1200"
  by (oc_eval oc_nc_1200)

lemma oc_nc_1201: "oc_sub None 1201"
  by (oc_eval oc_nc_1201)

lemma oc_nc_1202: "oc_sub None 1202"
  by (oc_eval oc_nc_1202)

lemma oc_nc_1203: "oc_sub None 1203"
  by (oc_eval oc_nc_1203)

lemma oc_nc_1204: "oc_sub None 1204"
  by (oc_eval oc_nc_1204)

lemma oc_nc_1205: "oc_sub None 1205"
  by (oc_eval oc_nc_1205)

lemma oc_nc_1206: "oc_sub None 1206"
  by (oc_eval oc_nc_1206)

lemma oc_nc_1207: "oc_sub None 1207"
  by (oc_eval oc_nc_1207)

lemma oc_nc_1208: "oc_sub None 1208"
  by (oc_eval oc_nc_1208)

lemma oc_nc_1209: "oc_sub None 1209"
  by (oc_eval oc_nc_1209)

lemma oc_nc_1210: "oc_sub None 1210"
  by (oc_eval oc_nc_1210)

lemma oc_nc_1211: "oc_sub None 1211"
  by (oc_eval oc_nc_1211)

lemma oc_nc_1212: "oc_sub None 1212"
  by (oc_eval oc_nc_1212)

lemma oc_nc_1213: "oc_sub None 1213"
  by (oc_eval oc_nc_1213)

lemma oc_nc_1214: "oc_sub None 1214"
  by (oc_eval oc_nc_1214)

lemma oc_nc_1215: "oc_sub None 1215"
  by (oc_eval oc_nc_1215)

lemma upt_nc_075: "[1200..<1216] = [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]"
  by (simp add: upt_rec)

lemma sec_nc_075: "\<forall>j\<in>{16 * 75..<16 * 75 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 75..<16 * 75 + 16}"
  then have "j \<in> set [1200..<1216]" unfolding set_upt by simp
  then have "j \<in> set [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]" unfolding upt_nc_075 .
  then show "oc_sub None j" using oc_nc_1200 oc_nc_1201 oc_nc_1202 oc_nc_1203 oc_nc_1204 oc_nc_1205 oc_nc_1206 oc_nc_1207 oc_nc_1208 oc_nc_1209 oc_nc_1210 oc_nc_1211 oc_nc_1212 oc_nc_1213 oc_nc_1214 oc_nc_1215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
