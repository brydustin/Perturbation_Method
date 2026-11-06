theory DCX_c30_140
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2240: "dc_sub dc_b30 2240"
  by (dc_eval dc_c30_2240)

lemma dc_c30_2241: "dc_sub dc_b30 2241"
  by (dc_eval dc_c30_2241)

lemma dc_c30_2242: "dc_sub dc_b30 2242"
  by (dc_eval dc_c30_2242)

lemma dc_c30_2243: "dc_sub dc_b30 2243"
  by (dc_eval dc_c30_2243)

lemma dc_c30_2244: "dc_sub dc_b30 2244"
  by (dc_eval dc_c30_2244)

lemma dc_c30_2245: "dc_sub dc_b30 2245"
  by (dc_eval dc_c30_2245)

lemma dc_c30_2246: "dc_sub dc_b30 2246"
  by (dc_eval dc_c30_2246)

lemma dc_c30_2247: "dc_sub dc_b30 2247"
  by (dc_eval dc_c30_2247)

lemma dc_c30_2248: "dc_sub dc_b30 2248"
  by (dc_eval dc_c30_2248)

lemma dc_c30_2249: "dc_sub dc_b30 2249"
  by (dc_eval dc_c30_2249)

lemma dc_c30_2250: "dc_sub dc_b30 2250"
  by (dc_eval dc_c30_2250)

lemma dc_c30_2251: "dc_sub dc_b30 2251"
  by (dc_eval dc_c30_2251)

lemma dc_c30_2252: "dc_sub dc_b30 2252"
  by (dc_eval dc_c30_2252)

lemma dc_c30_2253: "dc_sub dc_b30 2253"
  by (dc_eval dc_c30_2253)

lemma dc_c30_2254: "dc_sub dc_b30 2254"
  by (dc_eval dc_c30_2254)

lemma dc_c30_2255: "dc_sub dc_b30 2255"
  by (dc_eval dc_c30_2255)

lemma upt_c30_140: "[2240..<2256] = [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]"
  by (simp add: upt_rec)

lemma sec_c30_140: "\<forall>j\<in>{16 * 140..<16 * 140 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 140..<16 * 140 + 16}"
  then have "j \<in> set [2240..<2256]" unfolding set_upt by simp
  then have "j \<in> set [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]" unfolding upt_c30_140 .
  then show "dc_sub dc_b30 j" using dc_c30_2240 dc_c30_2241 dc_c30_2242 dc_c30_2243 dc_c30_2244 dc_c30_2245 dc_c30_2246 dc_c30_2247 dc_c30_2248 dc_c30_2249 dc_c30_2250 dc_c30_2251 dc_c30_2252 dc_c30_2253 dc_c30_2254 dc_c30_2255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
