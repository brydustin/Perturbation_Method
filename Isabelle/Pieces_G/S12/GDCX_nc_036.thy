theory GDCX_nc_036
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0576: "gdc_sub None 576"
  by (gdc_eval gdc_nc_0576)

lemma gdc_nc_0577: "gdc_sub None 577"
  by (gdc_eval gdc_nc_0577)

lemma gdc_nc_0578: "gdc_sub None 578"
  by (gdc_eval gdc_nc_0578)

lemma gdc_nc_0579: "gdc_sub None 579"
  by (gdc_eval gdc_nc_0579)

lemma gdc_nc_0580: "gdc_sub None 580"
  by (gdc_eval gdc_nc_0580)

lemma gdc_nc_0581: "gdc_sub None 581"
  by (gdc_eval gdc_nc_0581)

lemma gdc_nc_0582: "gdc_sub None 582"
  by (gdc_eval gdc_nc_0582)

lemma gdc_nc_0583: "gdc_sub None 583"
  by (gdc_eval gdc_nc_0583)

lemma gdc_nc_0584: "gdc_sub None 584"
  by (gdc_eval gdc_nc_0584)

lemma gdc_nc_0585: "gdc_sub None 585"
  by (gdc_eval gdc_nc_0585)

lemma gdc_nc_0586: "gdc_sub None 586"
  by (gdc_eval gdc_nc_0586)

lemma gdc_nc_0587: "gdc_sub None 587"
  by (gdc_eval gdc_nc_0587)

lemma gdc_nc_0588: "gdc_sub None 588"
  by (gdc_eval gdc_nc_0588)

lemma gdc_nc_0589: "gdc_sub None 589"
  by (gdc_eval gdc_nc_0589)

lemma gdc_nc_0590: "gdc_sub None 590"
  by (gdc_eval gdc_nc_0590)

lemma gdc_nc_0591: "gdc_sub None 591"
  by (gdc_eval gdc_nc_0591)

lemma gupt_nc_036: "[576..<592] = [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]"
  by (simp add: upt_rec)

lemma gsec_nc_036: "\<forall>j\<in>{16 * 36..<16 * 36 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 36..<16 * 36 + 16}"
  then have "j \<in> set [576..<592]" unfolding set_upt by simp
  then have "j \<in> set [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]" unfolding gupt_nc_036 .
  then show "gdc_sub None j" using gdc_nc_0576 gdc_nc_0577 gdc_nc_0578 gdc_nc_0579 gdc_nc_0580 gdc_nc_0581 gdc_nc_0582 gdc_nc_0583 gdc_nc_0584 gdc_nc_0585 gdc_nc_0586 gdc_nc_0587 gdc_nc_0588 gdc_nc_0589 gdc_nc_0590 gdc_nc_0591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
