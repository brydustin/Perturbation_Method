theory DCX_c30_015
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0240: "dc_sub dc_b30 240"
  by (dc_eval dc_c30_0240)

lemma dc_c30_0241: "dc_sub dc_b30 241"
  by (dc_eval dc_c30_0241)

lemma dc_c30_0242: "dc_sub dc_b30 242"
  by (dc_eval dc_c30_0242)

lemma dc_c30_0243: "dc_sub dc_b30 243"
  by (dc_eval dc_c30_0243)

lemma dc_c30_0244: "dc_sub dc_b30 244"
  by (dc_eval dc_c30_0244)

lemma dc_c30_0245: "dc_sub dc_b30 245"
  by (dc_eval dc_c30_0245)

lemma dc_c30_0246: "dc_sub dc_b30 246"
  by (dc_eval dc_c30_0246)

lemma dc_c30_0247: "dc_sub dc_b30 247"
  by (dc_eval dc_c30_0247)

lemma dc_c30_0248: "dc_sub dc_b30 248"
  by (dc_eval dc_c30_0248)

lemma dc_c30_0249: "dc_sub dc_b30 249"
  by (dc_eval dc_c30_0249)

lemma dc_c30_0250: "dc_sub dc_b30 250"
  by (dc_eval dc_c30_0250)

lemma dc_c30_0251: "dc_sub dc_b30 251"
  by (dc_eval dc_c30_0251)

lemma dc_c30_0252: "dc_sub dc_b30 252"
  by (dc_eval dc_c30_0252)

lemma dc_c30_0253: "dc_sub dc_b30 253"
  by (dc_eval dc_c30_0253)

lemma dc_c30_0254: "dc_sub dc_b30 254"
  by (dc_eval dc_c30_0254)

lemma dc_c30_0255: "dc_sub dc_b30 255"
  by (dc_eval dc_c30_0255)

lemma upt_c30_015: "[240..<256] = [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]"
  by (simp add: upt_rec)

lemma sec_c30_015: "\<forall>j\<in>{16 * 15..<16 * 15 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 15..<16 * 15 + 16}"
  then have "j \<in> set [240..<256]" unfolding set_upt by simp
  then have "j \<in> set [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]" unfolding upt_c30_015 .
  then show "dc_sub dc_b30 j" using dc_c30_0240 dc_c30_0241 dc_c30_0242 dc_c30_0243 dc_c30_0244 dc_c30_0245 dc_c30_0246 dc_c30_0247 dc_c30_0248 dc_c30_0249 dc_c30_0250 dc_c30_0251 dc_c30_0252 dc_c30_0253 dc_c30_0254 dc_c30_0255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
