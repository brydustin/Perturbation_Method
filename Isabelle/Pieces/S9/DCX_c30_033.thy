theory DCX_c30_033
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0528: "dc_sub dc_b30 528"
  by (dc_eval dc_c30_0528)

lemma dc_c30_0529: "dc_sub dc_b30 529"
  by (dc_eval dc_c30_0529)

lemma dc_c30_0530: "dc_sub dc_b30 530"
  by (dc_eval dc_c30_0530)

lemma dc_c30_0531: "dc_sub dc_b30 531"
  by (dc_eval dc_c30_0531)

lemma dc_c30_0532: "dc_sub dc_b30 532"
  by (dc_eval dc_c30_0532)

lemma dc_c30_0533: "dc_sub dc_b30 533"
  by (dc_eval dc_c30_0533)

lemma dc_c30_0534: "dc_sub dc_b30 534"
  by (dc_eval dc_c30_0534)

lemma dc_c30_0535: "dc_sub dc_b30 535"
  by (dc_eval dc_c30_0535)

lemma dc_c30_0536: "dc_sub dc_b30 536"
  by (dc_eval dc_c30_0536)

lemma dc_c30_0537: "dc_sub dc_b30 537"
  by (dc_eval dc_c30_0537)

lemma dc_c30_0538: "dc_sub dc_b30 538"
  by (dc_eval dc_c30_0538)

lemma dc_c30_0539: "dc_sub dc_b30 539"
  by (dc_eval dc_c30_0539)

lemma dc_c30_0540: "dc_sub dc_b30 540"
  by (dc_eval dc_c30_0540)

lemma dc_c30_0541: "dc_sub dc_b30 541"
  by (dc_eval dc_c30_0541)

lemma dc_c30_0542: "dc_sub dc_b30 542"
  by (dc_eval dc_c30_0542)

lemma dc_c30_0543: "dc_sub dc_b30 543"
  by (dc_eval dc_c30_0543)

lemma upt_c30_033: "[528..<544] = [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]"
  by (simp add: upt_rec)

lemma sec_c30_033: "\<forall>j\<in>{16 * 33..<16 * 33 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 33..<16 * 33 + 16}"
  then have "j \<in> set [528..<544]" unfolding set_upt by simp
  then have "j \<in> set [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]" unfolding upt_c30_033 .
  then show "dc_sub dc_b30 j" using dc_c30_0528 dc_c30_0529 dc_c30_0530 dc_c30_0531 dc_c30_0532 dc_c30_0533 dc_c30_0534 dc_c30_0535 dc_c30_0536 dc_c30_0537 dc_c30_0538 dc_c30_0539 dc_c30_0540 dc_c30_0541 dc_c30_0542 dc_c30_0543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
