theory GDCX_nc_151
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2416: "gdc_sub None 2416"
  by (gdc_eval gdc_nc_2416)

lemma gdc_nc_2417: "gdc_sub None 2417"
  by (gdc_eval gdc_nc_2417)

lemma gdc_nc_2418: "gdc_sub None 2418"
  by (gdc_eval gdc_nc_2418)

lemma gdc_nc_2419: "gdc_sub None 2419"
  by (gdc_eval gdc_nc_2419)

lemma gdc_nc_2420: "gdc_sub None 2420"
  by (gdc_eval gdc_nc_2420)

lemma gdc_nc_2421: "gdc_sub None 2421"
  by (gdc_eval gdc_nc_2421)

lemma gdc_nc_2422: "gdc_sub None 2422"
  by (gdc_eval gdc_nc_2422)

lemma gdc_nc_2423: "gdc_sub None 2423"
  by (gdc_eval gdc_nc_2423)

lemma gdc_nc_2424: "gdc_sub None 2424"
  by (gdc_eval gdc_nc_2424)

lemma gdc_nc_2425: "gdc_sub None 2425"
  by (gdc_eval gdc_nc_2425)

lemma gdc_nc_2426: "gdc_sub None 2426"
  by (gdc_eval gdc_nc_2426)

lemma gdc_nc_2427: "gdc_sub None 2427"
  by (gdc_eval gdc_nc_2427)

lemma gdc_nc_2428: "gdc_sub None 2428"
  by (gdc_eval gdc_nc_2428)

lemma gdc_nc_2429: "gdc_sub None 2429"
  by (gdc_eval gdc_nc_2429)

lemma gdc_nc_2430: "gdc_sub None 2430"
  by (gdc_eval gdc_nc_2430)

lemma gdc_nc_2431: "gdc_sub None 2431"
  by (gdc_eval gdc_nc_2431)

lemma gupt_nc_151: "[2416..<2432] = [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]"
  by (simp add: upt_rec)

lemma gsec_nc_151: "\<forall>j\<in>{16 * 151..<16 * 151 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 151..<16 * 151 + 16}"
  then have "j \<in> set [2416..<2432]" unfolding set_upt by simp
  then have "j \<in> set [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]" unfolding gupt_nc_151 .
  then show "gdc_sub None j" using gdc_nc_2416 gdc_nc_2417 gdc_nc_2418 gdc_nc_2419 gdc_nc_2420 gdc_nc_2421 gdc_nc_2422 gdc_nc_2423 gdc_nc_2424 gdc_nc_2425 gdc_nc_2426 gdc_nc_2427 gdc_nc_2428 gdc_nc_2429 gdc_nc_2430 gdc_nc_2431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
