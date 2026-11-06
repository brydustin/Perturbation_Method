theory GOCX_nc_033
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0528: "goc_sub None 528"
  by (goc_eval goc_nc_0528)

lemma goc_nc_0529: "goc_sub None 529"
  by (goc_eval goc_nc_0529)

lemma goc_nc_0530: "goc_sub None 530"
  by (goc_eval goc_nc_0530)

lemma goc_nc_0531: "goc_sub None 531"
  by (goc_eval goc_nc_0531)

lemma goc_nc_0532: "goc_sub None 532"
  by (goc_eval goc_nc_0532)

lemma goc_nc_0533: "goc_sub None 533"
  by (goc_eval goc_nc_0533)

lemma goc_nc_0534: "goc_sub None 534"
  by (goc_eval goc_nc_0534)

lemma goc_nc_0535: "goc_sub None 535"
  by (goc_eval goc_nc_0535)

lemma goc_nc_0536: "goc_sub None 536"
  by (goc_eval goc_nc_0536)

lemma goc_nc_0537: "goc_sub None 537"
  by (goc_eval goc_nc_0537)

lemma goc_nc_0538: "goc_sub None 538"
  by (goc_eval goc_nc_0538)

lemma goc_nc_0539: "goc_sub None 539"
  by (goc_eval goc_nc_0539)

lemma goc_nc_0540: "goc_sub None 540"
  by (goc_eval goc_nc_0540)

lemma goc_nc_0541: "goc_sub None 541"
  by (goc_eval goc_nc_0541)

lemma goc_nc_0542: "goc_sub None 542"
  by (goc_eval goc_nc_0542)

lemma goc_nc_0543: "goc_sub None 543"
  by (goc_eval goc_nc_0543)

lemma gupt_nc_033: "[528..<544] = [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]"
  by (simp add: upt_rec)

lemma gsec_nc_033: "\<forall>j\<in>{16 * 33..<16 * 33 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 33..<16 * 33 + 16}"
  then have "j \<in> set [528..<544]" unfolding set_upt by simp
  then have "j \<in> set [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]" unfolding gupt_nc_033 .
  then show "goc_sub None j" using goc_nc_0528 goc_nc_0529 goc_nc_0530 goc_nc_0531 goc_nc_0532 goc_nc_0533 goc_nc_0534 goc_nc_0535 goc_nc_0536 goc_nc_0537 goc_nc_0538 goc_nc_0539 goc_nc_0540 goc_nc_0541 goc_nc_0542 goc_nc_0543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
