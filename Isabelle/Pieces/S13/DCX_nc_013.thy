theory DCX_nc_013
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0208: "dc_sub None 208"
  by (dc_eval dc_nc_0208)

lemma dc_nc_0209: "dc_sub None 209"
  by (dc_eval dc_nc_0209)

lemma dc_nc_0210: "dc_sub None 210"
  by (dc_eval dc_nc_0210)

lemma dc_nc_0211: "dc_sub None 211"
  by (dc_eval dc_nc_0211)

lemma dc_nc_0212: "dc_sub None 212"
  by (dc_eval dc_nc_0212)

lemma dc_nc_0213: "dc_sub None 213"
  by (dc_eval dc_nc_0213)

lemma dc_nc_0214: "dc_sub None 214"
  by (dc_eval dc_nc_0214)

lemma dc_nc_0215: "dc_sub None 215"
  by (dc_eval dc_nc_0215)

lemma dc_nc_0216: "dc_sub None 216"
  by (dc_eval dc_nc_0216)

lemma dc_nc_0217: "dc_sub None 217"
  by (dc_eval dc_nc_0217)

lemma dc_nc_0218: "dc_sub None 218"
  by (dc_eval dc_nc_0218)

lemma dc_nc_0219: "dc_sub None 219"
  by (dc_eval dc_nc_0219)

lemma dc_nc_0220: "dc_sub None 220"
  by (dc_eval dc_nc_0220)

lemma dc_nc_0221: "dc_sub None 221"
  by (dc_eval dc_nc_0221)

lemma dc_nc_0222: "dc_sub None 222"
  by (dc_eval dc_nc_0222)

lemma dc_nc_0223: "dc_sub None 223"
  by (dc_eval dc_nc_0223)

lemma upt_nc_013: "[208..<224] = [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]"
  by (simp add: upt_rec)

lemma sec_nc_013: "\<forall>j\<in>{16 * 13..<16 * 13 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 13..<16 * 13 + 16}"
  then have "j \<in> set [208..<224]" unfolding set_upt by simp
  then have "j \<in> set [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]" unfolding upt_nc_013 .
  then show "dc_sub None j" using dc_nc_0208 dc_nc_0209 dc_nc_0210 dc_nc_0211 dc_nc_0212 dc_nc_0213 dc_nc_0214 dc_nc_0215 dc_nc_0216 dc_nc_0217 dc_nc_0218 dc_nc_0219 dc_nc_0220 dc_nc_0221 dc_nc_0222 dc_nc_0223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
