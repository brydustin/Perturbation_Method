theory OCX_c30_013
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0208: "oc_sub oc_b30 208"
  by (oc_eval oc_c30_0208)

lemma oc_c30_0209: "oc_sub oc_b30 209"
  by (oc_eval oc_c30_0209)

lemma oc_c30_0210: "oc_sub oc_b30 210"
  by (oc_eval oc_c30_0210)

lemma oc_c30_0211: "oc_sub oc_b30 211"
  by (oc_eval oc_c30_0211)

lemma oc_c30_0212: "oc_sub oc_b30 212"
  by (oc_eval oc_c30_0212)

lemma oc_c30_0213: "oc_sub oc_b30 213"
  by (oc_eval oc_c30_0213)

lemma oc_c30_0214: "oc_sub oc_b30 214"
  by (oc_eval oc_c30_0214)

lemma oc_c30_0215: "oc_sub oc_b30 215"
  by (oc_eval oc_c30_0215)

lemma oc_c30_0216: "oc_sub oc_b30 216"
  by (oc_eval oc_c30_0216)

lemma oc_c30_0217: "oc_sub oc_b30 217"
  by (oc_eval oc_c30_0217)

lemma oc_c30_0218: "oc_sub oc_b30 218"
  by (oc_eval oc_c30_0218)

lemma oc_c30_0219: "oc_sub oc_b30 219"
  by (oc_eval oc_c30_0219)

lemma oc_c30_0220: "oc_sub oc_b30 220"
  by (oc_eval oc_c30_0220)

lemma oc_c30_0221: "oc_sub oc_b30 221"
  by (oc_eval oc_c30_0221)

lemma oc_c30_0222: "oc_sub oc_b30 222"
  by (oc_eval oc_c30_0222)

lemma oc_c30_0223: "oc_sub oc_b30 223"
  by (oc_eval oc_c30_0223)

lemma upt_c30_013: "[208..<224] = [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]"
  by (simp add: upt_rec)

lemma sec_c30_013: "\<forall>j\<in>{16 * 13..<16 * 13 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 13..<16 * 13 + 16}"
  then have "j \<in> set [208..<224]" unfolding set_upt by simp
  then have "j \<in> set [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]" unfolding upt_c30_013 .
  then show "oc_sub oc_b30 j" using oc_c30_0208 oc_c30_0209 oc_c30_0210 oc_c30_0211 oc_c30_0212 oc_c30_0213 oc_c30_0214 oc_c30_0215 oc_c30_0216 oc_c30_0217 oc_c30_0218 oc_c30_0219 oc_c30_0220 oc_c30_0221 oc_c30_0222 oc_c30_0223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
