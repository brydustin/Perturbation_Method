theory OCX_c30_004
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0064: "oc_sub oc_b30 64"
  by (oc_eval oc_c30_0064)

lemma oc_c30_0065: "oc_sub oc_b30 65"
  by (oc_eval oc_c30_0065)

lemma oc_c30_0066: "oc_sub oc_b30 66"
  by (oc_eval oc_c30_0066)

lemma oc_c30_0067: "oc_sub oc_b30 67"
  by (oc_eval oc_c30_0067)

lemma oc_c30_0068: "oc_sub oc_b30 68"
  by (oc_eval oc_c30_0068)

lemma oc_c30_0069: "oc_sub oc_b30 69"
  by (oc_eval oc_c30_0069)

lemma oc_c30_0070: "oc_sub oc_b30 70"
  by (oc_eval oc_c30_0070)

lemma oc_c30_0071: "oc_sub oc_b30 71"
  by (oc_eval oc_c30_0071)

lemma oc_c30_0072: "oc_sub oc_b30 72"
  by (oc_eval oc_c30_0072)

lemma oc_c30_0073: "oc_sub oc_b30 73"
  by (oc_eval oc_c30_0073)

lemma oc_c30_0074: "oc_sub oc_b30 74"
  by (oc_eval oc_c30_0074)

lemma oc_c30_0075: "oc_sub oc_b30 75"
  by (oc_eval oc_c30_0075)

lemma oc_c30_0076: "oc_sub oc_b30 76"
  by (oc_eval oc_c30_0076)

lemma oc_c30_0077: "oc_sub oc_b30 77"
  by (oc_eval oc_c30_0077)

lemma oc_c30_0078: "oc_sub oc_b30 78"
  by (oc_eval oc_c30_0078)

lemma oc_c30_0079: "oc_sub oc_b30 79"
  by (oc_eval oc_c30_0079)

lemma upt_c30_004: "[64..<80] = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]"
  by (simp add: upt_rec)

lemma sec_c30_004: "\<forall>j\<in>{16 * 4..<16 * 4 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 4..<16 * 4 + 16}"
  then have "j \<in> set [64..<80]" unfolding set_upt by simp
  then have "j \<in> set [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]" unfolding upt_c30_004 .
  then show "oc_sub oc_b30 j" using oc_c30_0064 oc_c30_0065 oc_c30_0066 oc_c30_0067 oc_c30_0068 oc_c30_0069 oc_c30_0070 oc_c30_0071 oc_c30_0072 oc_c30_0073 oc_c30_0074 oc_c30_0075 oc_c30_0076 oc_c30_0077 oc_c30_0078 oc_c30_0079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
