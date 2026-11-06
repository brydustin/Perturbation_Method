theory DCX_c30_036
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0576: "dc_sub dc_b30 576"
  by (dc_eval dc_c30_0576)

lemma dc_c30_0577: "dc_sub dc_b30 577"
  by (dc_eval dc_c30_0577)

lemma dc_c30_0578: "dc_sub dc_b30 578"
  by (dc_eval dc_c30_0578)

lemma dc_c30_0579: "dc_sub dc_b30 579"
  by (dc_eval dc_c30_0579)

lemma dc_c30_0580: "dc_sub dc_b30 580"
  by (dc_eval dc_c30_0580)

lemma dc_c30_0581: "dc_sub dc_b30 581"
  by (dc_eval dc_c30_0581)

lemma dc_c30_0582: "dc_sub dc_b30 582"
  by (dc_eval dc_c30_0582)

lemma dc_c30_0583: "dc_sub dc_b30 583"
  by (dc_eval dc_c30_0583)

lemma dc_c30_0584: "dc_sub dc_b30 584"
  by (dc_eval dc_c30_0584)

lemma dc_c30_0585: "dc_sub dc_b30 585"
  by (dc_eval dc_c30_0585)

lemma dc_c30_0586: "dc_sub dc_b30 586"
  by (dc_eval dc_c30_0586)

lemma dc_c30_0587: "dc_sub dc_b30 587"
  by (dc_eval dc_c30_0587)

lemma dc_c30_0588: "dc_sub dc_b30 588"
  by (dc_eval dc_c30_0588)

lemma dc_c30_0589: "dc_sub dc_b30 589"
  by (dc_eval dc_c30_0589)

lemma dc_c30_0590: "dc_sub dc_b30 590"
  by (dc_eval dc_c30_0590)

lemma dc_c30_0591: "dc_sub dc_b30 591"
  by (dc_eval dc_c30_0591)

lemma upt_c30_036: "[576..<592] = [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]"
  by (simp add: upt_rec)

lemma sec_c30_036: "\<forall>j\<in>{16 * 36..<16 * 36 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 36..<16 * 36 + 16}"
  then have "j \<in> set [576..<592]" unfolding set_upt by simp
  then have "j \<in> set [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]" unfolding upt_c30_036 .
  then show "dc_sub dc_b30 j" using dc_c30_0576 dc_c30_0577 dc_c30_0578 dc_c30_0579 dc_c30_0580 dc_c30_0581 dc_c30_0582 dc_c30_0583 dc_c30_0584 dc_c30_0585 dc_c30_0586 dc_c30_0587 dc_c30_0588 dc_c30_0589 dc_c30_0590 dc_c30_0591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
