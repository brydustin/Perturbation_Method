theory DCX_nc_146
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2336: "dc_sub None 2336"
  by (dc_eval dc_nc_2336)

lemma dc_nc_2337: "dc_sub None 2337"
  by (dc_eval dc_nc_2337)

lemma dc_nc_2338: "dc_sub None 2338"
  by (dc_eval dc_nc_2338)

lemma dc_nc_2339: "dc_sub None 2339"
  by (dc_eval dc_nc_2339)

lemma dc_nc_2340: "dc_sub None 2340"
  by (dc_eval dc_nc_2340)

lemma dc_nc_2341: "dc_sub None 2341"
  by (dc_eval dc_nc_2341)

lemma dc_nc_2342: "dc_sub None 2342"
  by (dc_eval dc_nc_2342)

lemma dc_nc_2343: "dc_sub None 2343"
  by (dc_eval dc_nc_2343)

lemma dc_nc_2344: "dc_sub None 2344"
  by (dc_eval dc_nc_2344)

lemma dc_nc_2345: "dc_sub None 2345"
  by (dc_eval dc_nc_2345)

lemma dc_nc_2346: "dc_sub None 2346"
  by (dc_eval dc_nc_2346)

lemma dc_nc_2347: "dc_sub None 2347"
  by (dc_eval dc_nc_2347)

lemma dc_nc_2348: "dc_sub None 2348"
  by (dc_eval dc_nc_2348)

lemma dc_nc_2349: "dc_sub None 2349"
  by (dc_eval dc_nc_2349)

lemma dc_nc_2350: "dc_sub None 2350"
  by (dc_eval dc_nc_2350)

lemma dc_nc_2351: "dc_sub None 2351"
  by (dc_eval dc_nc_2351)

lemma upt_nc_146: "[2336..<2352] = [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]"
  by (simp add: upt_rec)

lemma sec_nc_146: "\<forall>j\<in>{16 * 146..<16 * 146 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 146..<16 * 146 + 16}"
  then have "j \<in> set [2336..<2352]" unfolding set_upt by simp
  then have "j \<in> set [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]" unfolding upt_nc_146 .
  then show "dc_sub None j" using dc_nc_2336 dc_nc_2337 dc_nc_2338 dc_nc_2339 dc_nc_2340 dc_nc_2341 dc_nc_2342 dc_nc_2343 dc_nc_2344 dc_nc_2345 dc_nc_2346 dc_nc_2347 dc_nc_2348 dc_nc_2349 dc_nc_2350 dc_nc_2351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
