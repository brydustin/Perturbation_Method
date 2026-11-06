theory GOCX_nc_013
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0208: "goc_sub None 208"
  by (goc_eval goc_nc_0208)

lemma goc_nc_0209: "goc_sub None 209"
  by (goc_eval goc_nc_0209)

lemma goc_nc_0210: "goc_sub None 210"
  by (goc_eval goc_nc_0210)

lemma goc_nc_0211: "goc_sub None 211"
  by (goc_eval goc_nc_0211)

lemma goc_nc_0212: "goc_sub None 212"
  by (goc_eval goc_nc_0212)

lemma goc_nc_0213: "goc_sub None 213"
  by (goc_eval goc_nc_0213)

lemma goc_nc_0214: "goc_sub None 214"
  by (goc_eval goc_nc_0214)

lemma goc_nc_0215: "goc_sub None 215"
  by (goc_eval goc_nc_0215)

lemma goc_nc_0216: "goc_sub None 216"
  by (goc_eval goc_nc_0216)

lemma goc_nc_0217: "goc_sub None 217"
  by (goc_eval goc_nc_0217)

lemma goc_nc_0218: "goc_sub None 218"
  by (goc_eval goc_nc_0218)

lemma goc_nc_0219: "goc_sub None 219"
  by (goc_eval goc_nc_0219)

lemma goc_nc_0220: "goc_sub None 220"
  by (goc_eval goc_nc_0220)

lemma goc_nc_0221: "goc_sub None 221"
  by (goc_eval goc_nc_0221)

lemma goc_nc_0222: "goc_sub None 222"
  by (goc_eval goc_nc_0222)

lemma goc_nc_0223: "goc_sub None 223"
  by (goc_eval goc_nc_0223)

lemma gupt_nc_013: "[208..<224] = [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]"
  by (simp add: upt_rec)

lemma gsec_nc_013: "\<forall>j\<in>{16 * 13..<16 * 13 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 13..<16 * 13 + 16}"
  then have "j \<in> set [208..<224]" unfolding set_upt by simp
  then have "j \<in> set [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]" unfolding gupt_nc_013 .
  then show "goc_sub None j" using goc_nc_0208 goc_nc_0209 goc_nc_0210 goc_nc_0211 goc_nc_0212 goc_nc_0213 goc_nc_0214 goc_nc_0215 goc_nc_0216 goc_nc_0217 goc_nc_0218 goc_nc_0219 goc_nc_0220 goc_nc_0221 goc_nc_0222 goc_nc_0223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
