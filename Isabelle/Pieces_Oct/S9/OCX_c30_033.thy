theory OCX_c30_033
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0528: "oc_sub oc_b30 528"
  by (oc_eval oc_c30_0528)

lemma oc_c30_0529: "oc_sub oc_b30 529"
  by (oc_eval oc_c30_0529)

lemma oc_c30_0530: "oc_sub oc_b30 530"
  by (oc_eval oc_c30_0530)

lemma oc_c30_0531: "oc_sub oc_b30 531"
  by (oc_eval oc_c30_0531)

lemma oc_c30_0532: "oc_sub oc_b30 532"
  by (oc_eval oc_c30_0532)

lemma oc_c30_0533: "oc_sub oc_b30 533"
  by (oc_eval oc_c30_0533)

lemma oc_c30_0534: "oc_sub oc_b30 534"
  by (oc_eval oc_c30_0534)

lemma oc_c30_0535: "oc_sub oc_b30 535"
  by (oc_eval oc_c30_0535)

lemma oc_c30_0536: "oc_sub oc_b30 536"
  by (oc_eval oc_c30_0536)

lemma oc_c30_0537: "oc_sub oc_b30 537"
  by (oc_eval oc_c30_0537)

lemma oc_c30_0538: "oc_sub oc_b30 538"
  by (oc_eval oc_c30_0538)

lemma oc_c30_0539: "oc_sub oc_b30 539"
  by (oc_eval oc_c30_0539)

lemma oc_c30_0540: "oc_sub oc_b30 540"
  by (oc_eval oc_c30_0540)

lemma oc_c30_0541: "oc_sub oc_b30 541"
  by (oc_eval oc_c30_0541)

lemma oc_c30_0542: "oc_sub oc_b30 542"
  by (oc_eval oc_c30_0542)

lemma oc_c30_0543: "oc_sub oc_b30 543"
  by (oc_eval oc_c30_0543)

lemma upt_c30_033: "[528..<544] = [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]"
  by (simp add: upt_rec)

lemma sec_c30_033: "\<forall>j\<in>{16 * 33..<16 * 33 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 33..<16 * 33 + 16}"
  then have "j \<in> set [528..<544]" unfolding set_upt by simp
  then have "j \<in> set [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]" unfolding upt_c30_033 .
  then show "oc_sub oc_b30 j" using oc_c30_0528 oc_c30_0529 oc_c30_0530 oc_c30_0531 oc_c30_0532 oc_c30_0533 oc_c30_0534 oc_c30_0535 oc_c30_0536 oc_c30_0537 oc_c30_0538 oc_c30_0539 oc_c30_0540 oc_c30_0541 oc_c30_0542 oc_c30_0543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
