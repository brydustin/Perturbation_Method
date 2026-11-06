theory OCX_nc_140
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2240: "oc_sub None 2240"
  by (oc_eval oc_nc_2240)

lemma oc_nc_2241: "oc_sub None 2241"
  by (oc_eval oc_nc_2241)

lemma oc_nc_2242: "oc_sub None 2242"
  by (oc_eval oc_nc_2242)

lemma oc_nc_2243: "oc_sub None 2243"
  by (oc_eval oc_nc_2243)

lemma oc_nc_2244: "oc_sub None 2244"
  by (oc_eval oc_nc_2244)

lemma oc_nc_2245: "oc_sub None 2245"
  by (oc_eval oc_nc_2245)

lemma oc_nc_2246: "oc_sub None 2246"
  by (oc_eval oc_nc_2246)

lemma oc_nc_2247: "oc_sub None 2247"
  by (oc_eval oc_nc_2247)

lemma oc_nc_2248: "oc_sub None 2248"
  by (oc_eval oc_nc_2248)

lemma oc_nc_2249: "oc_sub None 2249"
  by (oc_eval oc_nc_2249)

lemma oc_nc_2250: "oc_sub None 2250"
  by (oc_eval oc_nc_2250)

lemma oc_nc_2251: "oc_sub None 2251"
  by (oc_eval oc_nc_2251)

lemma oc_nc_2252: "oc_sub None 2252"
  by (oc_eval oc_nc_2252)

lemma oc_nc_2253: "oc_sub None 2253"
  by (oc_eval oc_nc_2253)

lemma oc_nc_2254: "oc_sub None 2254"
  by (oc_eval oc_nc_2254)

lemma oc_nc_2255: "oc_sub None 2255"
  by (oc_eval oc_nc_2255)

lemma upt_nc_140: "[2240..<2256] = [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]"
  by (simp add: upt_rec)

lemma sec_nc_140: "\<forall>j\<in>{16 * 140..<16 * 140 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 140..<16 * 140 + 16}"
  then have "j \<in> set [2240..<2256]" unfolding set_upt by simp
  then have "j \<in> set [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]" unfolding upt_nc_140 .
  then show "oc_sub None j" using oc_nc_2240 oc_nc_2241 oc_nc_2242 oc_nc_2243 oc_nc_2244 oc_nc_2245 oc_nc_2246 oc_nc_2247 oc_nc_2248 oc_nc_2249 oc_nc_2250 oc_nc_2251 oc_nc_2252 oc_nc_2253 oc_nc_2254 oc_nc_2255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
