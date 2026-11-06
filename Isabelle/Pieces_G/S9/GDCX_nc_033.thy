theory GDCX_nc_033
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0528: "gdc_sub None 528"
  by (gdc_eval gdc_nc_0528)

lemma gdc_nc_0529: "gdc_sub None 529"
  by (gdc_eval gdc_nc_0529)

lemma gdc_nc_0530: "gdc_sub None 530"
  by (gdc_eval gdc_nc_0530)

lemma gdc_nc_0531: "gdc_sub None 531"
  by (gdc_eval gdc_nc_0531)

lemma gdc_nc_0532: "gdc_sub None 532"
  by (gdc_eval gdc_nc_0532)

lemma gdc_nc_0533: "gdc_sub None 533"
  by (gdc_eval gdc_nc_0533)

lemma gdc_nc_0534: "gdc_sub None 534"
  by (gdc_eval gdc_nc_0534)

lemma gdc_nc_0535: "gdc_sub None 535"
  by (gdc_eval gdc_nc_0535)

lemma gdc_nc_0536: "gdc_sub None 536"
  by (gdc_eval gdc_nc_0536)

lemma gdc_nc_0537: "gdc_sub None 537"
  by (gdc_eval gdc_nc_0537)

lemma gdc_nc_0538: "gdc_sub None 538"
  by (gdc_eval gdc_nc_0538)

lemma gdc_nc_0539: "gdc_sub None 539"
  by (gdc_eval gdc_nc_0539)

lemma gdc_nc_0540: "gdc_sub None 540"
  by (gdc_eval gdc_nc_0540)

lemma gdc_nc_0541: "gdc_sub None 541"
  by (gdc_eval gdc_nc_0541)

lemma gdc_nc_0542: "gdc_sub None 542"
  by (gdc_eval gdc_nc_0542)

lemma gdc_nc_0543: "gdc_sub None 543"
  by (gdc_eval gdc_nc_0543)

lemma gupt_nc_033: "[528..<544] = [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]"
  by (simp add: upt_rec)

lemma gsec_nc_033: "\<forall>j\<in>{16 * 33..<16 * 33 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 33..<16 * 33 + 16}"
  then have "j \<in> set [528..<544]" unfolding set_upt by simp
  then have "j \<in> set [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]" unfolding gupt_nc_033 .
  then show "gdc_sub None j" using gdc_nc_0528 gdc_nc_0529 gdc_nc_0530 gdc_nc_0531 gdc_nc_0532 gdc_nc_0533 gdc_nc_0534 gdc_nc_0535 gdc_nc_0536 gdc_nc_0537 gdc_nc_0538 gdc_nc_0539 gdc_nc_0540 gdc_nc_0541 gdc_nc_0542 gdc_nc_0543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
