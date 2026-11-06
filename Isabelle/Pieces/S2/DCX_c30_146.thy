theory DCX_c30_146
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2336: "dc_sub dc_b30 2336"
  by (dc_eval dc_c30_2336)

lemma dc_c30_2337: "dc_sub dc_b30 2337"
  by (dc_eval dc_c30_2337)

lemma dc_c30_2338: "dc_sub dc_b30 2338"
  by (dc_eval dc_c30_2338)

lemma dc_c30_2339: "dc_sub dc_b30 2339"
  by (dc_eval dc_c30_2339)

lemma dc_c30_2340: "dc_sub dc_b30 2340"
  by (dc_eval dc_c30_2340)

lemma dc_c30_2341: "dc_sub dc_b30 2341"
  by (dc_eval dc_c30_2341)

lemma dc_c30_2342: "dc_sub dc_b30 2342"
  by (dc_eval dc_c30_2342)

lemma dc_c30_2343: "dc_sub dc_b30 2343"
  by (dc_eval dc_c30_2343)

lemma dc_c30_2344: "dc_sub dc_b30 2344"
  by (dc_eval dc_c30_2344)

lemma dc_c30_2345: "dc_sub dc_b30 2345"
  by (dc_eval dc_c30_2345)

lemma dc_c30_2346: "dc_sub dc_b30 2346"
  by (dc_eval dc_c30_2346)

lemma dc_c30_2347: "dc_sub dc_b30 2347"
  by (dc_eval dc_c30_2347)

lemma dc_c30_2348: "dc_sub dc_b30 2348"
  by (dc_eval dc_c30_2348)

lemma dc_c30_2349: "dc_sub dc_b30 2349"
  by (dc_eval dc_c30_2349)

lemma dc_c30_2350: "dc_sub dc_b30 2350"
  by (dc_eval dc_c30_2350)

lemma dc_c30_2351: "dc_sub dc_b30 2351"
  by (dc_eval dc_c30_2351)

lemma upt_c30_146: "[2336..<2352] = [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]"
  by (simp add: upt_rec)

lemma sec_c30_146: "\<forall>j\<in>{16 * 146..<16 * 146 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 146..<16 * 146 + 16}"
  then have "j \<in> set [2336..<2352]" unfolding set_upt by simp
  then have "j \<in> set [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]" unfolding upt_c30_146 .
  then show "dc_sub dc_b30 j" using dc_c30_2336 dc_c30_2337 dc_c30_2338 dc_c30_2339 dc_c30_2340 dc_c30_2341 dc_c30_2342 dc_c30_2343 dc_c30_2344 dc_c30_2345 dc_c30_2346 dc_c30_2347 dc_c30_2348 dc_c30_2349 dc_c30_2350 dc_c30_2351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
