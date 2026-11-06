theory DCX_c30_013
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0208: "dc_sub dc_b30 208"
  by (dc_eval dc_c30_0208)

lemma dc_c30_0209: "dc_sub dc_b30 209"
  by (dc_eval dc_c30_0209)

lemma dc_c30_0210: "dc_sub dc_b30 210"
  by (dc_eval dc_c30_0210)

lemma dc_c30_0211: "dc_sub dc_b30 211"
  by (dc_eval dc_c30_0211)

lemma dc_c30_0212: "dc_sub dc_b30 212"
  by (dc_eval dc_c30_0212)

lemma dc_c30_0213: "dc_sub dc_b30 213"
  by (dc_eval dc_c30_0213)

lemma dc_c30_0214: "dc_sub dc_b30 214"
  by (dc_eval dc_c30_0214)

lemma dc_c30_0215: "dc_sub dc_b30 215"
  by (dc_eval dc_c30_0215)

lemma dc_c30_0216: "dc_sub dc_b30 216"
  by (dc_eval dc_c30_0216)

lemma dc_c30_0217: "dc_sub dc_b30 217"
  by (dc_eval dc_c30_0217)

lemma dc_c30_0218: "dc_sub dc_b30 218"
  by (dc_eval dc_c30_0218)

lemma dc_c30_0219: "dc_sub dc_b30 219"
  by (dc_eval dc_c30_0219)

lemma dc_c30_0220: "dc_sub dc_b30 220"
  by (dc_eval dc_c30_0220)

lemma dc_c30_0221: "dc_sub dc_b30 221"
  by (dc_eval dc_c30_0221)

lemma dc_c30_0222: "dc_sub dc_b30 222"
  by (dc_eval dc_c30_0222)

lemma dc_c30_0223: "dc_sub dc_b30 223"
  by (dc_eval dc_c30_0223)

lemma upt_c30_013: "[208..<224] = [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]"
  by (simp add: upt_rec)

lemma sec_c30_013: "\<forall>j\<in>{16 * 13..<16 * 13 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 13..<16 * 13 + 16}"
  then have "j \<in> set [208..<224]" unfolding set_upt by simp
  then have "j \<in> set [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]" unfolding upt_c30_013 .
  then show "dc_sub dc_b30 j" using dc_c30_0208 dc_c30_0209 dc_c30_0210 dc_c30_0211 dc_c30_0212 dc_c30_0213 dc_c30_0214 dc_c30_0215 dc_c30_0216 dc_c30_0217 dc_c30_0218 dc_c30_0219 dc_c30_0220 dc_c30_0221 dc_c30_0222 dc_c30_0223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
