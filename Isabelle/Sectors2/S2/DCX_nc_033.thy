theory DCX_nc_033
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0528: "dc_sub None 528"
  by (dc_eval dc_nc_0528)

lemma dc_nc_0529: "dc_sub None 529"
  by (dc_eval dc_nc_0529)

lemma dc_nc_0530: "dc_sub None 530"
  by (dc_eval dc_nc_0530)

lemma dc_nc_0531: "dc_sub None 531"
  by (dc_eval dc_nc_0531)

lemma dc_nc_0532: "dc_sub None 532"
  by (dc_eval dc_nc_0532)

lemma dc_nc_0533: "dc_sub None 533"
  by (dc_eval dc_nc_0533)

lemma dc_nc_0534: "dc_sub None 534"
  by (dc_eval dc_nc_0534)

lemma dc_nc_0535: "dc_sub None 535"
  by (dc_eval dc_nc_0535)

lemma dc_nc_0536: "dc_sub None 536"
  by (dc_eval dc_nc_0536)

lemma dc_nc_0537: "dc_sub None 537"
  by (dc_eval dc_nc_0537)

lemma dc_nc_0538: "dc_sub None 538"
  by (dc_eval dc_nc_0538)

lemma dc_nc_0539: "dc_sub None 539"
  by (dc_eval dc_nc_0539)

lemma dc_nc_0540: "dc_sub None 540"
  by (dc_eval dc_nc_0540)

lemma dc_nc_0541: "dc_sub None 541"
  by (dc_eval dc_nc_0541)

lemma dc_nc_0542: "dc_sub None 542"
  by (dc_eval dc_nc_0542)

lemma dc_nc_0543: "dc_sub None 543"
  by (dc_eval dc_nc_0543)

lemma upt_nc_033: "[528..<544] = [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]"
  by (simp add: upt_rec)

lemma sec_nc_033: "\<forall>j\<in>{16 * 33..<16 * 33 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 33..<16 * 33 + 16}"
  then have "j \<in> set [528..<544]" unfolding set_upt by simp
  then have "j \<in> set [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]" unfolding upt_nc_033 .
  then show "dc_sub None j" using dc_nc_0528 dc_nc_0529 dc_nc_0530 dc_nc_0531 dc_nc_0532 dc_nc_0533 dc_nc_0534 dc_nc_0535 dc_nc_0536 dc_nc_0537 dc_nc_0538 dc_nc_0539 dc_nc_0540 dc_nc_0541 dc_nc_0542 dc_nc_0543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
