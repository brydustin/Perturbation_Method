theory OCX_nc_146
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2336: "oc_sub None 2336"
  by (oc_eval oc_nc_2336)

lemma oc_nc_2337: "oc_sub None 2337"
  by (oc_eval oc_nc_2337)

lemma oc_nc_2338: "oc_sub None 2338"
  by (oc_eval oc_nc_2338)

lemma oc_nc_2339: "oc_sub None 2339"
  by (oc_eval oc_nc_2339)

lemma oc_nc_2340: "oc_sub None 2340"
  by (oc_eval oc_nc_2340)

lemma oc_nc_2341: "oc_sub None 2341"
  by (oc_eval oc_nc_2341)

lemma oc_nc_2342: "oc_sub None 2342"
  by (oc_eval oc_nc_2342)

lemma oc_nc_2343: "oc_sub None 2343"
  by (oc_eval oc_nc_2343)

lemma oc_nc_2344: "oc_sub None 2344"
  by (oc_eval oc_nc_2344)

lemma oc_nc_2345: "oc_sub None 2345"
  by (oc_eval oc_nc_2345)

lemma oc_nc_2346: "oc_sub None 2346"
  by (oc_eval oc_nc_2346)

lemma oc_nc_2347: "oc_sub None 2347"
  by (oc_eval oc_nc_2347)

lemma oc_nc_2348: "oc_sub None 2348"
  by (oc_eval oc_nc_2348)

lemma oc_nc_2349: "oc_sub None 2349"
  by (oc_eval oc_nc_2349)

lemma oc_nc_2350: "oc_sub None 2350"
  by (oc_eval oc_nc_2350)

lemma oc_nc_2351: "oc_sub None 2351"
  by (oc_eval oc_nc_2351)

lemma upt_nc_146: "[2336..<2352] = [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]"
  by (simp add: upt_rec)

lemma sec_nc_146: "\<forall>j\<in>{16 * 146..<16 * 146 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 146..<16 * 146 + 16}"
  then have "j \<in> set [2336..<2352]" unfolding set_upt by simp
  then have "j \<in> set [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]" unfolding upt_nc_146 .
  then show "oc_sub None j" using oc_nc_2336 oc_nc_2337 oc_nc_2338 oc_nc_2339 oc_nc_2340 oc_nc_2341 oc_nc_2342 oc_nc_2343 oc_nc_2344 oc_nc_2345 oc_nc_2346 oc_nc_2347 oc_nc_2348 oc_nc_2349 oc_nc_2350 oc_nc_2351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
