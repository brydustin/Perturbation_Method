theory GOCX_nc_036
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0576: "goc_sub None 576"
  by (goc_eval goc_nc_0576)

lemma goc_nc_0577: "goc_sub None 577"
  by (goc_eval goc_nc_0577)

lemma goc_nc_0578: "goc_sub None 578"
  by (goc_eval goc_nc_0578)

lemma goc_nc_0579: "goc_sub None 579"
  by (goc_eval goc_nc_0579)

lemma goc_nc_0580: "goc_sub None 580"
  by (goc_eval goc_nc_0580)

lemma goc_nc_0581: "goc_sub None 581"
  by (goc_eval goc_nc_0581)

lemma goc_nc_0582: "goc_sub None 582"
  by (goc_eval goc_nc_0582)

lemma goc_nc_0583: "goc_sub None 583"
  by (goc_eval goc_nc_0583)

lemma goc_nc_0584: "goc_sub None 584"
  by (goc_eval goc_nc_0584)

lemma goc_nc_0585: "goc_sub None 585"
  by (goc_eval goc_nc_0585)

lemma goc_nc_0586: "goc_sub None 586"
  by (goc_eval goc_nc_0586)

lemma goc_nc_0587: "goc_sub None 587"
  by (goc_eval goc_nc_0587)

lemma goc_nc_0588: "goc_sub None 588"
  by (goc_eval goc_nc_0588)

lemma goc_nc_0589: "goc_sub None 589"
  by (goc_eval goc_nc_0589)

lemma goc_nc_0590: "goc_sub None 590"
  by (goc_eval goc_nc_0590)

lemma goc_nc_0591: "goc_sub None 591"
  by (goc_eval goc_nc_0591)

lemma gupt_nc_036: "[576..<592] = [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]"
  by (simp add: upt_rec)

lemma gsec_nc_036: "\<forall>j\<in>{16 * 36..<16 * 36 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 36..<16 * 36 + 16}"
  then have "j \<in> set [576..<592]" unfolding set_upt by simp
  then have "j \<in> set [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]" unfolding gupt_nc_036 .
  then show "goc_sub None j" using goc_nc_0576 goc_nc_0577 goc_nc_0578 goc_nc_0579 goc_nc_0580 goc_nc_0581 goc_nc_0582 goc_nc_0583 goc_nc_0584 goc_nc_0585 goc_nc_0586 goc_nc_0587 goc_nc_0588 goc_nc_0589 goc_nc_0590 goc_nc_0591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
