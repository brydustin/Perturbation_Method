theory OCX_nc_033
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0528: "oc_sub None 528"
  by (oc_eval oc_nc_0528)

lemma oc_nc_0529: "oc_sub None 529"
  by (oc_eval oc_nc_0529)

lemma oc_nc_0530: "oc_sub None 530"
  by (oc_eval oc_nc_0530)

lemma oc_nc_0531: "oc_sub None 531"
  by (oc_eval oc_nc_0531)

lemma oc_nc_0532: "oc_sub None 532"
  by (oc_eval oc_nc_0532)

lemma oc_nc_0533: "oc_sub None 533"
  by (oc_eval oc_nc_0533)

lemma oc_nc_0534: "oc_sub None 534"
  by (oc_eval oc_nc_0534)

lemma oc_nc_0535: "oc_sub None 535"
  by (oc_eval oc_nc_0535)

lemma oc_nc_0536: "oc_sub None 536"
  by (oc_eval oc_nc_0536)

lemma oc_nc_0537: "oc_sub None 537"
  by (oc_eval oc_nc_0537)

lemma oc_nc_0538: "oc_sub None 538"
  by (oc_eval oc_nc_0538)

lemma oc_nc_0539: "oc_sub None 539"
  by (oc_eval oc_nc_0539)

lemma oc_nc_0540: "oc_sub None 540"
  by (oc_eval oc_nc_0540)

lemma oc_nc_0541: "oc_sub None 541"
  by (oc_eval oc_nc_0541)

lemma oc_nc_0542: "oc_sub None 542"
  by (oc_eval oc_nc_0542)

lemma oc_nc_0543: "oc_sub None 543"
  by (oc_eval oc_nc_0543)

lemma upt_nc_033: "[528..<544] = [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]"
  by (simp add: upt_rec)

lemma sec_nc_033: "\<forall>j\<in>{16 * 33..<16 * 33 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 33..<16 * 33 + 16}"
  then have "j \<in> set [528..<544]" unfolding set_upt by simp
  then have "j \<in> set [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]" unfolding upt_nc_033 .
  then show "oc_sub None j" using oc_nc_0528 oc_nc_0529 oc_nc_0530 oc_nc_0531 oc_nc_0532 oc_nc_0533 oc_nc_0534 oc_nc_0535 oc_nc_0536 oc_nc_0537 oc_nc_0538 oc_nc_0539 oc_nc_0540 oc_nc_0541 oc_nc_0542 oc_nc_0543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
