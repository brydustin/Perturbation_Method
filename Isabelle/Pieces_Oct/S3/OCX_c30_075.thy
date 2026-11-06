theory OCX_c30_075
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1200: "oc_sub oc_b30 1200"
  by (oc_eval oc_c30_1200)

lemma oc_c30_1201: "oc_sub oc_b30 1201"
  by (oc_eval oc_c30_1201)

lemma oc_c30_1202: "oc_sub oc_b30 1202"
  by (oc_eval oc_c30_1202)

lemma oc_c30_1203: "oc_sub oc_b30 1203"
  by (oc_eval oc_c30_1203)

lemma oc_c30_1204: "oc_sub oc_b30 1204"
  by (oc_eval oc_c30_1204)

lemma oc_c30_1205: "oc_sub oc_b30 1205"
  by (oc_eval oc_c30_1205)

lemma oc_c30_1206: "oc_sub oc_b30 1206"
  by (oc_eval oc_c30_1206)

lemma oc_c30_1207: "oc_sub oc_b30 1207"
  by (oc_eval oc_c30_1207)

lemma oc_c30_1208: "oc_sub oc_b30 1208"
  by (oc_eval oc_c30_1208)

lemma oc_c30_1209: "oc_sub oc_b30 1209"
  by (oc_eval oc_c30_1209)

lemma oc_c30_1210: "oc_sub oc_b30 1210"
  by (oc_eval oc_c30_1210)

lemma oc_c30_1211: "oc_sub oc_b30 1211"
  by (oc_eval oc_c30_1211)

lemma oc_c30_1212: "oc_sub oc_b30 1212"
  by (oc_eval oc_c30_1212)

lemma oc_c30_1213: "oc_sub oc_b30 1213"
  by (oc_eval oc_c30_1213)

lemma oc_c30_1214: "oc_sub oc_b30 1214"
  by (oc_eval oc_c30_1214)

lemma oc_c30_1215: "oc_sub oc_b30 1215"
  by (oc_eval oc_c30_1215)

lemma upt_c30_075: "[1200..<1216] = [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]"
  by (simp add: upt_rec)

lemma sec_c30_075: "\<forall>j\<in>{16 * 75..<16 * 75 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 75..<16 * 75 + 16}"
  then have "j \<in> set [1200..<1216]" unfolding set_upt by simp
  then have "j \<in> set [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]" unfolding upt_c30_075 .
  then show "oc_sub oc_b30 j" using oc_c30_1200 oc_c30_1201 oc_c30_1202 oc_c30_1203 oc_c30_1204 oc_c30_1205 oc_c30_1206 oc_c30_1207 oc_c30_1208 oc_c30_1209 oc_c30_1210 oc_c30_1211 oc_c30_1212 oc_c30_1213 oc_c30_1214 oc_c30_1215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
