theory OCX_nc_036
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0576: "oc_sub None 576"
  by (oc_eval oc_nc_0576)

lemma oc_nc_0577: "oc_sub None 577"
  by (oc_eval oc_nc_0577)

lemma oc_nc_0578: "oc_sub None 578"
  by (oc_eval oc_nc_0578)

lemma oc_nc_0579: "oc_sub None 579"
  by (oc_eval oc_nc_0579)

lemma oc_nc_0580: "oc_sub None 580"
  by (oc_eval oc_nc_0580)

lemma oc_nc_0581: "oc_sub None 581"
  by (oc_eval oc_nc_0581)

lemma oc_nc_0582: "oc_sub None 582"
  by (oc_eval oc_nc_0582)

lemma oc_nc_0583: "oc_sub None 583"
  by (oc_eval oc_nc_0583)

lemma oc_nc_0584: "oc_sub None 584"
  by (oc_eval oc_nc_0584)

lemma oc_nc_0585: "oc_sub None 585"
  by (oc_eval oc_nc_0585)

lemma oc_nc_0586: "oc_sub None 586"
  by (oc_eval oc_nc_0586)

lemma oc_nc_0587: "oc_sub None 587"
  by (oc_eval oc_nc_0587)

lemma oc_nc_0588: "oc_sub None 588"
  by (oc_eval oc_nc_0588)

lemma oc_nc_0589: "oc_sub None 589"
  by (oc_eval oc_nc_0589)

lemma oc_nc_0590: "oc_sub None 590"
  by (oc_eval oc_nc_0590)

lemma oc_nc_0591: "oc_sub None 591"
  by (oc_eval oc_nc_0591)

lemma upt_nc_036: "[576..<592] = [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]"
  by (simp add: upt_rec)

lemma sec_nc_036: "\<forall>j\<in>{16 * 36..<16 * 36 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 36..<16 * 36 + 16}"
  then have "j \<in> set [576..<592]" unfolding set_upt by simp
  then have "j \<in> set [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]" unfolding upt_nc_036 .
  then show "oc_sub None j" using oc_nc_0576 oc_nc_0577 oc_nc_0578 oc_nc_0579 oc_nc_0580 oc_nc_0581 oc_nc_0582 oc_nc_0583 oc_nc_0584 oc_nc_0585 oc_nc_0586 oc_nc_0587 oc_nc_0588 oc_nc_0589 oc_nc_0590 oc_nc_0591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
