theory DCX_nc_016
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0256: "dc_sub None 256"
  by (dc_eval dc_nc_0256)

lemma dc_nc_0257: "dc_sub None 257"
  by (dc_eval dc_nc_0257)

lemma dc_nc_0258: "dc_sub None 258"
  by (dc_eval dc_nc_0258)

lemma dc_nc_0259: "dc_sub None 259"
  by (dc_eval dc_nc_0259)

lemma dc_nc_0260: "dc_sub None 260"
  by (dc_eval dc_nc_0260)

lemma dc_nc_0261: "dc_sub None 261"
  by (dc_eval dc_nc_0261)

lemma dc_nc_0262: "dc_sub None 262"
  by (dc_eval dc_nc_0262)

lemma dc_nc_0263: "dc_sub None 263"
  by (dc_eval dc_nc_0263)

lemma dc_nc_0264: "dc_sub None 264"
  by (dc_eval dc_nc_0264)

lemma dc_nc_0265: "dc_sub None 265"
  by (dc_eval dc_nc_0265)

lemma dc_nc_0266: "dc_sub None 266"
  by (dc_eval dc_nc_0266)

lemma dc_nc_0267: "dc_sub None 267"
  by (dc_eval dc_nc_0267)

lemma dc_nc_0268: "dc_sub None 268"
  by (dc_eval dc_nc_0268)

lemma dc_nc_0269: "dc_sub None 269"
  by (dc_eval dc_nc_0269)

lemma dc_nc_0270: "dc_sub None 270"
  by (dc_eval dc_nc_0270)

lemma dc_nc_0271: "dc_sub None 271"
  by (dc_eval dc_nc_0271)

lemma upt_nc_016: "[256..<272] = [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]"
  by (simp add: upt_rec)

lemma sec_nc_016: "\<forall>j\<in>{16 * 16..<16 * 16 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 16..<16 * 16 + 16}"
  then have "j \<in> set [256..<272]" unfolding set_upt by simp
  then have "j \<in> set [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]" unfolding upt_nc_016 .
  then show "dc_sub None j" using dc_nc_0256 dc_nc_0257 dc_nc_0258 dc_nc_0259 dc_nc_0260 dc_nc_0261 dc_nc_0262 dc_nc_0263 dc_nc_0264 dc_nc_0265 dc_nc_0266 dc_nc_0267 dc_nc_0268 dc_nc_0269 dc_nc_0270 dc_nc_0271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
