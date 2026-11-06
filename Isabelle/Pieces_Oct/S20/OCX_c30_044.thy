theory OCX_c30_044
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0704: "oc_sub oc_b30 704"
  by (oc_eval oc_c30_0704)

lemma oc_c30_0705: "oc_sub oc_b30 705"
  by (oc_eval oc_c30_0705)

lemma oc_c30_0706: "oc_sub oc_b30 706"
  by (oc_eval oc_c30_0706)

lemma oc_c30_0707: "oc_sub oc_b30 707"
  by (oc_eval oc_c30_0707)

lemma oc_c30_0708: "oc_sub oc_b30 708"
  by (oc_eval oc_c30_0708)

lemma oc_c30_0709: "oc_sub oc_b30 709"
  by (oc_eval oc_c30_0709)

lemma oc_c30_0710: "oc_sub oc_b30 710"
  by (oc_eval oc_c30_0710)

lemma oc_c30_0711: "oc_sub oc_b30 711"
  by (oc_eval oc_c30_0711)

lemma oc_c30_0712: "oc_sub oc_b30 712"
  by (oc_eval oc_c30_0712)

lemma oc_c30_0713: "oc_sub oc_b30 713"
  by (oc_eval oc_c30_0713)

lemma oc_c30_0714: "oc_sub oc_b30 714"
  by (oc_eval oc_c30_0714)

lemma oc_c30_0715: "oc_sub oc_b30 715"
  by (oc_eval oc_c30_0715)

lemma oc_c30_0716: "oc_sub oc_b30 716"
  by (oc_eval oc_c30_0716)

lemma oc_c30_0717: "oc_sub oc_b30 717"
  by (oc_eval oc_c30_0717)

lemma oc_c30_0718: "oc_sub oc_b30 718"
  by (oc_eval oc_c30_0718)

lemma oc_c30_0719: "oc_sub oc_b30 719"
  by (oc_eval oc_c30_0719)

lemma upt_c30_044: "[704..<720] = [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]"
  by (simp add: upt_rec)

lemma sec_c30_044: "\<forall>j\<in>{16 * 44..<16 * 44 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 44..<16 * 44 + 16}"
  then have "j \<in> set [704..<720]" unfolding set_upt by simp
  then have "j \<in> set [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]" unfolding upt_c30_044 .
  then show "oc_sub oc_b30 j" using oc_c30_0704 oc_c30_0705 oc_c30_0706 oc_c30_0707 oc_c30_0708 oc_c30_0709 oc_c30_0710 oc_c30_0711 oc_c30_0712 oc_c30_0713 oc_c30_0714 oc_c30_0715 oc_c30_0716 oc_c30_0717 oc_c30_0718 oc_c30_0719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
