theory DCX_nc_036
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0576: "dc_sub None 576"
  by (dc_eval dc_nc_0576)

lemma dc_nc_0577: "dc_sub None 577"
  by (dc_eval dc_nc_0577)

lemma dc_nc_0578: "dc_sub None 578"
  by (dc_eval dc_nc_0578)

lemma dc_nc_0579: "dc_sub None 579"
  by (dc_eval dc_nc_0579)

lemma dc_nc_0580: "dc_sub None 580"
  by (dc_eval dc_nc_0580)

lemma dc_nc_0581: "dc_sub None 581"
  by (dc_eval dc_nc_0581)

lemma dc_nc_0582: "dc_sub None 582"
  by (dc_eval dc_nc_0582)

lemma dc_nc_0583: "dc_sub None 583"
  by (dc_eval dc_nc_0583)

lemma dc_nc_0584: "dc_sub None 584"
  by (dc_eval dc_nc_0584)

lemma dc_nc_0585: "dc_sub None 585"
  by (dc_eval dc_nc_0585)

lemma dc_nc_0586: "dc_sub None 586"
  by (dc_eval dc_nc_0586)

lemma dc_nc_0587: "dc_sub None 587"
  by (dc_eval dc_nc_0587)

lemma dc_nc_0588: "dc_sub None 588"
  by (dc_eval dc_nc_0588)

lemma dc_nc_0589: "dc_sub None 589"
  by (dc_eval dc_nc_0589)

lemma dc_nc_0590: "dc_sub None 590"
  by (dc_eval dc_nc_0590)

lemma dc_nc_0591: "dc_sub None 591"
  by (dc_eval dc_nc_0591)

lemma upt_nc_036: "[576..<592] = [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]"
  by (simp add: upt_rec)

lemma sec_nc_036: "\<forall>j\<in>{16 * 36..<16 * 36 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 36..<16 * 36 + 16}"
  then have "j \<in> set [576..<592]" unfolding set_upt by simp
  then have "j \<in> set [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]" unfolding upt_nc_036 .
  then show "dc_sub None j" using dc_nc_0576 dc_nc_0577 dc_nc_0578 dc_nc_0579 dc_nc_0580 dc_nc_0581 dc_nc_0582 dc_nc_0583 dc_nc_0584 dc_nc_0585 dc_nc_0586 dc_nc_0587 dc_nc_0588 dc_nc_0589 dc_nc_0590 dc_nc_0591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
