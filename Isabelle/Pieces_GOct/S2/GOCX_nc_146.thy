theory GOCX_nc_146
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2336: "goc_sub None 2336"
  by (goc_eval goc_nc_2336)

lemma goc_nc_2337: "goc_sub None 2337"
  by (goc_eval goc_nc_2337)

lemma goc_nc_2338: "goc_sub None 2338"
  by (goc_eval goc_nc_2338)

lemma goc_nc_2339: "goc_sub None 2339"
  by (goc_eval goc_nc_2339)

lemma goc_nc_2340: "goc_sub None 2340"
  by (goc_eval goc_nc_2340)

lemma goc_nc_2341: "goc_sub None 2341"
  by (goc_eval goc_nc_2341)

lemma goc_nc_2342: "goc_sub None 2342"
  by (goc_eval goc_nc_2342)

lemma goc_nc_2343: "goc_sub None 2343"
  by (goc_eval goc_nc_2343)

lemma goc_nc_2344: "goc_sub None 2344"
  by (goc_eval goc_nc_2344)

lemma goc_nc_2345: "goc_sub None 2345"
  by (goc_eval goc_nc_2345)

lemma goc_nc_2346: "goc_sub None 2346"
  by (goc_eval goc_nc_2346)

lemma goc_nc_2347: "goc_sub None 2347"
  by (goc_eval goc_nc_2347)

lemma goc_nc_2348: "goc_sub None 2348"
  by (goc_eval goc_nc_2348)

lemma goc_nc_2349: "goc_sub None 2349"
  by (goc_eval goc_nc_2349)

lemma goc_nc_2350: "goc_sub None 2350"
  by (goc_eval goc_nc_2350)

lemma goc_nc_2351: "goc_sub None 2351"
  by (goc_eval goc_nc_2351)

lemma gupt_nc_146: "[2336..<2352] = [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]"
  by (simp add: upt_rec)

lemma gsec_nc_146: "\<forall>j\<in>{16 * 146..<16 * 146 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 146..<16 * 146 + 16}"
  then have "j \<in> set [2336..<2352]" unfolding set_upt by simp
  then have "j \<in> set [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]" unfolding gupt_nc_146 .
  then show "goc_sub None j" using goc_nc_2336 goc_nc_2337 goc_nc_2338 goc_nc_2339 goc_nc_2340 goc_nc_2341 goc_nc_2342 goc_nc_2343 goc_nc_2344 goc_nc_2345 goc_nc_2346 goc_nc_2347 goc_nc_2348 goc_nc_2349 goc_nc_2350 goc_nc_2351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
