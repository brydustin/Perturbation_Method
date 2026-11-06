theory OCX_c30_146
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2336: "oc_sub oc_b30 2336"
  by (oc_eval oc_c30_2336)

lemma oc_c30_2337: "oc_sub oc_b30 2337"
  by (oc_eval oc_c30_2337)

lemma oc_c30_2338: "oc_sub oc_b30 2338"
  by (oc_eval oc_c30_2338)

lemma oc_c30_2339: "oc_sub oc_b30 2339"
  by (oc_eval oc_c30_2339)

lemma oc_c30_2340: "oc_sub oc_b30 2340"
  by (oc_eval oc_c30_2340)

lemma oc_c30_2341: "oc_sub oc_b30 2341"
  by (oc_eval oc_c30_2341)

lemma oc_c30_2342: "oc_sub oc_b30 2342"
  by (oc_eval oc_c30_2342)

lemma oc_c30_2343: "oc_sub oc_b30 2343"
  by (oc_eval oc_c30_2343)

lemma oc_c30_2344: "oc_sub oc_b30 2344"
  by (oc_eval oc_c30_2344)

lemma oc_c30_2345: "oc_sub oc_b30 2345"
  by (oc_eval oc_c30_2345)

lemma oc_c30_2346: "oc_sub oc_b30 2346"
  by (oc_eval oc_c30_2346)

lemma oc_c30_2347: "oc_sub oc_b30 2347"
  by (oc_eval oc_c30_2347)

lemma oc_c30_2348: "oc_sub oc_b30 2348"
  by (oc_eval oc_c30_2348)

lemma oc_c30_2349: "oc_sub oc_b30 2349"
  by (oc_eval oc_c30_2349)

lemma oc_c30_2350: "oc_sub oc_b30 2350"
  by (oc_eval oc_c30_2350)

lemma oc_c30_2351: "oc_sub oc_b30 2351"
  by (oc_eval oc_c30_2351)

lemma upt_c30_146: "[2336..<2352] = [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]"
  by (simp add: upt_rec)

lemma sec_c30_146: "\<forall>j\<in>{16 * 146..<16 * 146 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 146..<16 * 146 + 16}"
  then have "j \<in> set [2336..<2352]" unfolding set_upt by simp
  then have "j \<in> set [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]" unfolding upt_c30_146 .
  then show "oc_sub oc_b30 j" using oc_c30_2336 oc_c30_2337 oc_c30_2338 oc_c30_2339 oc_c30_2340 oc_c30_2341 oc_c30_2342 oc_c30_2343 oc_c30_2344 oc_c30_2345 oc_c30_2346 oc_c30_2347 oc_c30_2348 oc_c30_2349 oc_c30_2350 oc_c30_2351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
