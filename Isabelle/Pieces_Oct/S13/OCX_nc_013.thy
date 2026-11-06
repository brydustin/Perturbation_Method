theory OCX_nc_013
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0208: "oc_sub None 208"
  by (oc_eval oc_nc_0208)

lemma oc_nc_0209: "oc_sub None 209"
  by (oc_eval oc_nc_0209)

lemma oc_nc_0210: "oc_sub None 210"
  by (oc_eval oc_nc_0210)

lemma oc_nc_0211: "oc_sub None 211"
  by (oc_eval oc_nc_0211)

lemma oc_nc_0212: "oc_sub None 212"
  by (oc_eval oc_nc_0212)

lemma oc_nc_0213: "oc_sub None 213"
  by (oc_eval oc_nc_0213)

lemma oc_nc_0214: "oc_sub None 214"
  by (oc_eval oc_nc_0214)

lemma oc_nc_0215: "oc_sub None 215"
  by (oc_eval oc_nc_0215)

lemma oc_nc_0216: "oc_sub None 216"
  by (oc_eval oc_nc_0216)

lemma oc_nc_0217: "oc_sub None 217"
  by (oc_eval oc_nc_0217)

lemma oc_nc_0218: "oc_sub None 218"
  by (oc_eval oc_nc_0218)

lemma oc_nc_0219: "oc_sub None 219"
  by (oc_eval oc_nc_0219)

lemma oc_nc_0220: "oc_sub None 220"
  by (oc_eval oc_nc_0220)

lemma oc_nc_0221: "oc_sub None 221"
  by (oc_eval oc_nc_0221)

lemma oc_nc_0222: "oc_sub None 222"
  by (oc_eval oc_nc_0222)

lemma oc_nc_0223: "oc_sub None 223"
  by (oc_eval oc_nc_0223)

lemma upt_nc_013: "[208..<224] = [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]"
  by (simp add: upt_rec)

lemma sec_nc_013: "\<forall>j\<in>{16 * 13..<16 * 13 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 13..<16 * 13 + 16}"
  then have "j \<in> set [208..<224]" unfolding set_upt by simp
  then have "j \<in> set [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]" unfolding upt_nc_013 .
  then show "oc_sub None j" using oc_nc_0208 oc_nc_0209 oc_nc_0210 oc_nc_0211 oc_nc_0212 oc_nc_0213 oc_nc_0214 oc_nc_0215 oc_nc_0216 oc_nc_0217 oc_nc_0218 oc_nc_0219 oc_nc_0220 oc_nc_0221 oc_nc_0222 oc_nc_0223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
