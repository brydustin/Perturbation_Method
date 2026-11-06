theory DCX_nc_093
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1488: "dc_sub None 1488"
  by (dc_eval dc_nc_1488)

lemma dc_nc_1489: "dc_sub None 1489"
  by (dc_eval dc_nc_1489)

lemma dc_nc_1490: "dc_sub None 1490"
  by (dc_eval dc_nc_1490)

lemma dc_nc_1491: "dc_sub None 1491"
  by (dc_eval dc_nc_1491)

lemma dc_nc_1492: "dc_sub None 1492"
  by (dc_eval dc_nc_1492)

lemma dc_nc_1493: "dc_sub None 1493"
  by (dc_eval dc_nc_1493)

lemma dc_nc_1494: "dc_sub None 1494"
  by (dc_eval dc_nc_1494)

lemma dc_nc_1495: "dc_sub None 1495"
  by (dc_eval dc_nc_1495)

lemma dc_nc_1496: "dc_sub None 1496"
  by (dc_eval dc_nc_1496)

lemma dc_nc_1497: "dc_sub None 1497"
  by (dc_eval dc_nc_1497)

lemma dc_nc_1498: "dc_sub None 1498"
  by (dc_eval dc_nc_1498)

lemma dc_nc_1499: "dc_sub None 1499"
  by (dc_eval dc_nc_1499)

lemma dc_nc_1500: "dc_sub None 1500"
  by (dc_eval dc_nc_1500)

lemma dc_nc_1501: "dc_sub None 1501"
  by (dc_eval dc_nc_1501)

lemma dc_nc_1502: "dc_sub None 1502"
  by (dc_eval dc_nc_1502)

lemma dc_nc_1503: "dc_sub None 1503"
  by (dc_eval dc_nc_1503)

lemma upt_nc_093: "[1488..<1504] = [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]"
  by (simp add: upt_rec)

lemma sec_nc_093: "\<forall>j\<in>{16 * 93..<16 * 93 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 93..<16 * 93 + 16}"
  then have "j \<in> set [1488..<1504]" unfolding set_upt by simp
  then have "j \<in> set [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]" unfolding upt_nc_093 .
  then show "dc_sub None j" using dc_nc_1488 dc_nc_1489 dc_nc_1490 dc_nc_1491 dc_nc_1492 dc_nc_1493 dc_nc_1494 dc_nc_1495 dc_nc_1496 dc_nc_1497 dc_nc_1498 dc_nc_1499 dc_nc_1500 dc_nc_1501 dc_nc_1502 dc_nc_1503
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
