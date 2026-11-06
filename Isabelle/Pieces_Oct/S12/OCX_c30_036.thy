theory OCX_c30_036
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0576: "oc_sub oc_b30 576"
  by (oc_eval oc_c30_0576)

lemma oc_c30_0577: "oc_sub oc_b30 577"
  by (oc_eval oc_c30_0577)

lemma oc_c30_0578: "oc_sub oc_b30 578"
  by (oc_eval oc_c30_0578)

lemma oc_c30_0579: "oc_sub oc_b30 579"
  by (oc_eval oc_c30_0579)

lemma oc_c30_0580: "oc_sub oc_b30 580"
  by (oc_eval oc_c30_0580)

lemma oc_c30_0581: "oc_sub oc_b30 581"
  by (oc_eval oc_c30_0581)

lemma oc_c30_0582: "oc_sub oc_b30 582"
  by (oc_eval oc_c30_0582)

lemma oc_c30_0583: "oc_sub oc_b30 583"
  by (oc_eval oc_c30_0583)

lemma oc_c30_0584: "oc_sub oc_b30 584"
  by (oc_eval oc_c30_0584)

lemma oc_c30_0585: "oc_sub oc_b30 585"
  by (oc_eval oc_c30_0585)

lemma oc_c30_0586: "oc_sub oc_b30 586"
  by (oc_eval oc_c30_0586)

lemma oc_c30_0587: "oc_sub oc_b30 587"
  by (oc_eval oc_c30_0587)

lemma oc_c30_0588: "oc_sub oc_b30 588"
  by (oc_eval oc_c30_0588)

lemma oc_c30_0589: "oc_sub oc_b30 589"
  by (oc_eval oc_c30_0589)

lemma oc_c30_0590: "oc_sub oc_b30 590"
  by (oc_eval oc_c30_0590)

lemma oc_c30_0591: "oc_sub oc_b30 591"
  by (oc_eval oc_c30_0591)

lemma upt_c30_036: "[576..<592] = [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]"
  by (simp add: upt_rec)

lemma sec_c30_036: "\<forall>j\<in>{16 * 36..<16 * 36 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 36..<16 * 36 + 16}"
  then have "j \<in> set [576..<592]" unfolding set_upt by simp
  then have "j \<in> set [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]" unfolding upt_c30_036 .
  then show "oc_sub oc_b30 j" using oc_c30_0576 oc_c30_0577 oc_c30_0578 oc_c30_0579 oc_c30_0580 oc_c30_0581 oc_c30_0582 oc_c30_0583 oc_c30_0584 oc_c30_0585 oc_c30_0586 oc_c30_0587 oc_c30_0588 oc_c30_0589 oc_c30_0590 oc_c30_0591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
