theory GOCX_nc_151
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2416: "goc_sub None 2416"
  by (goc_eval goc_nc_2416)

lemma goc_nc_2417: "goc_sub None 2417"
  by (goc_eval goc_nc_2417)

lemma goc_nc_2418: "goc_sub None 2418"
  by (goc_eval goc_nc_2418)

lemma goc_nc_2419: "goc_sub None 2419"
  by (goc_eval goc_nc_2419)

lemma goc_nc_2420: "goc_sub None 2420"
  by (goc_eval goc_nc_2420)

lemma goc_nc_2421: "goc_sub None 2421"
  by (goc_eval goc_nc_2421)

lemma goc_nc_2422: "goc_sub None 2422"
  by (goc_eval goc_nc_2422)

lemma goc_nc_2423: "goc_sub None 2423"
  by (goc_eval goc_nc_2423)

lemma goc_nc_2424: "goc_sub None 2424"
  by (goc_eval goc_nc_2424)

lemma goc_nc_2425: "goc_sub None 2425"
  by (goc_eval goc_nc_2425)

lemma goc_nc_2426: "goc_sub None 2426"
  by (goc_eval goc_nc_2426)

lemma goc_nc_2427: "goc_sub None 2427"
  by (goc_eval goc_nc_2427)

lemma goc_nc_2428: "goc_sub None 2428"
  by (goc_eval goc_nc_2428)

lemma goc_nc_2429: "goc_sub None 2429"
  by (goc_eval goc_nc_2429)

lemma goc_nc_2430: "goc_sub None 2430"
  by (goc_eval goc_nc_2430)

lemma goc_nc_2431: "goc_sub None 2431"
  by (goc_eval goc_nc_2431)

lemma gupt_nc_151: "[2416..<2432] = [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]"
  by (simp add: upt_rec)

lemma gsec_nc_151: "\<forall>j\<in>{16 * 151..<16 * 151 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 151..<16 * 151 + 16}"
  then have "j \<in> set [2416..<2432]" unfolding set_upt by simp
  then have "j \<in> set [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]" unfolding gupt_nc_151 .
  then show "goc_sub None j" using goc_nc_2416 goc_nc_2417 goc_nc_2418 goc_nc_2419 goc_nc_2420 goc_nc_2421 goc_nc_2422 goc_nc_2423 goc_nc_2424 goc_nc_2425 goc_nc_2426 goc_nc_2427 goc_nc_2428 goc_nc_2429 goc_nc_2430 goc_nc_2431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
