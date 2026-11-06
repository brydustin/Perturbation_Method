theory GDCX_nc_146
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2336: "gdc_sub None 2336"
  by (gdc_eval gdc_nc_2336)

lemma gdc_nc_2337: "gdc_sub None 2337"
  by (gdc_eval gdc_nc_2337)

lemma gdc_nc_2338: "gdc_sub None 2338"
  by (gdc_eval gdc_nc_2338)

lemma gdc_nc_2339: "gdc_sub None 2339"
  by (gdc_eval gdc_nc_2339)

lemma gdc_nc_2340: "gdc_sub None 2340"
  by (gdc_eval gdc_nc_2340)

lemma gdc_nc_2341: "gdc_sub None 2341"
  by (gdc_eval gdc_nc_2341)

lemma gdc_nc_2342: "gdc_sub None 2342"
  by (gdc_eval gdc_nc_2342)

lemma gdc_nc_2343: "gdc_sub None 2343"
  by (gdc_eval gdc_nc_2343)

lemma gdc_nc_2344: "gdc_sub None 2344"
  by (gdc_eval gdc_nc_2344)

lemma gdc_nc_2345: "gdc_sub None 2345"
  by (gdc_eval gdc_nc_2345)

lemma gdc_nc_2346: "gdc_sub None 2346"
  by (gdc_eval gdc_nc_2346)

lemma gdc_nc_2347: "gdc_sub None 2347"
  by (gdc_eval gdc_nc_2347)

lemma gdc_nc_2348: "gdc_sub None 2348"
  by (gdc_eval gdc_nc_2348)

lemma gdc_nc_2349: "gdc_sub None 2349"
  by (gdc_eval gdc_nc_2349)

lemma gdc_nc_2350: "gdc_sub None 2350"
  by (gdc_eval gdc_nc_2350)

lemma gdc_nc_2351: "gdc_sub None 2351"
  by (gdc_eval gdc_nc_2351)

lemma gupt_nc_146: "[2336..<2352] = [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]"
  by (simp add: upt_rec)

lemma gsec_nc_146: "\<forall>j\<in>{16 * 146..<16 * 146 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 146..<16 * 146 + 16}"
  then have "j \<in> set [2336..<2352]" unfolding set_upt by simp
  then have "j \<in> set [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]" unfolding gupt_nc_146 .
  then show "gdc_sub None j" using gdc_nc_2336 gdc_nc_2337 gdc_nc_2338 gdc_nc_2339 gdc_nc_2340 gdc_nc_2341 gdc_nc_2342 gdc_nc_2343 gdc_nc_2344 gdc_nc_2345 gdc_nc_2346 gdc_nc_2347 gdc_nc_2348 gdc_nc_2349 gdc_nc_2350 gdc_nc_2351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
