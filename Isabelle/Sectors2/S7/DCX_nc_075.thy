theory DCX_nc_075
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1200: "dc_sub None 1200"
  by (dc_eval dc_nc_1200)

lemma dc_nc_1201: "dc_sub None 1201"
  by (dc_eval dc_nc_1201)

lemma dc_nc_1202: "dc_sub None 1202"
  by (dc_eval dc_nc_1202)

lemma dc_nc_1203: "dc_sub None 1203"
  by (dc_eval dc_nc_1203)

lemma dc_nc_1204: "dc_sub None 1204"
  by (dc_eval dc_nc_1204)

lemma dc_nc_1205: "dc_sub None 1205"
  by (dc_eval dc_nc_1205)

lemma dc_nc_1206: "dc_sub None 1206"
  by (dc_eval dc_nc_1206)

lemma dc_nc_1207: "dc_sub None 1207"
  by (dc_eval dc_nc_1207)

lemma dc_nc_1208: "dc_sub None 1208"
  by (dc_eval dc_nc_1208)

lemma dc_nc_1209: "dc_sub None 1209"
  by (dc_eval dc_nc_1209)

lemma dc_nc_1210: "dc_sub None 1210"
  by (dc_eval dc_nc_1210)

lemma dc_nc_1211: "dc_sub None 1211"
  by (dc_eval dc_nc_1211)

lemma dc_nc_1212: "dc_sub None 1212"
  by (dc_eval dc_nc_1212)

lemma dc_nc_1213: "dc_sub None 1213"
  by (dc_eval dc_nc_1213)

lemma dc_nc_1214: "dc_sub None 1214"
  by (dc_eval dc_nc_1214)

lemma dc_nc_1215: "dc_sub None 1215"
  by (dc_eval dc_nc_1215)

lemma upt_nc_075: "[1200..<1216] = [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]"
  by (simp add: upt_rec)

lemma sec_nc_075: "\<forall>j\<in>{16 * 75..<16 * 75 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 75..<16 * 75 + 16}"
  then have "j \<in> set [1200..<1216]" unfolding set_upt by simp
  then have "j \<in> set [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]" unfolding upt_nc_075 .
  then show "dc_sub None j" using dc_nc_1200 dc_nc_1201 dc_nc_1202 dc_nc_1203 dc_nc_1204 dc_nc_1205 dc_nc_1206 dc_nc_1207 dc_nc_1208 dc_nc_1209 dc_nc_1210 dc_nc_1211 dc_nc_1212 dc_nc_1213 dc_nc_1214 dc_nc_1215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
