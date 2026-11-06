theory GOCX_nc_169
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2704: "goc_sub None 2704"
  by (goc_eval goc_nc_2704)

lemma goc_nc_2705: "goc_sub None 2705"
  by (goc_eval goc_nc_2705)

lemma goc_nc_2706: "goc_sub None 2706"
  by (goc_eval goc_nc_2706)

lemma goc_nc_2707: "goc_sub None 2707"
  by (goc_eval goc_nc_2707)

lemma goc_nc_2708: "goc_sub None 2708"
  by (goc_eval goc_nc_2708)

lemma goc_nc_2709: "goc_sub None 2709"
  by (goc_eval goc_nc_2709)

lemma goc_nc_2710: "goc_sub None 2710"
  by (goc_eval goc_nc_2710)

lemma goc_nc_2711: "goc_sub None 2711"
  by (goc_eval goc_nc_2711)

lemma goc_nc_2712: "goc_sub None 2712"
  by (goc_eval goc_nc_2712)

lemma goc_nc_2713: "goc_sub None 2713"
  by (goc_eval goc_nc_2713)

lemma goc_nc_2714: "goc_sub None 2714"
  by (goc_eval goc_nc_2714)

lemma goc_nc_2715: "goc_sub None 2715"
  by (goc_eval goc_nc_2715)

lemma goc_nc_2716: "goc_sub None 2716"
  by (goc_eval goc_nc_2716)

lemma goc_nc_2717: "goc_sub None 2717"
  by (goc_eval goc_nc_2717)

lemma goc_nc_2718: "goc_sub None 2718"
  by (goc_eval goc_nc_2718)

lemma goc_nc_2719: "goc_sub None 2719"
  by (goc_eval goc_nc_2719)

lemma gupt_nc_169: "[2704..<2720] = [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]"
  by (simp add: upt_rec)

lemma gsec_nc_169: "\<forall>j\<in>{16 * 169..<16 * 169 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 169..<16 * 169 + 16}"
  then have "j \<in> set [2704..<2720]" unfolding set_upt by simp
  then have "j \<in> set [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]" unfolding gupt_nc_169 .
  then show "goc_sub None j" using goc_nc_2704 goc_nc_2705 goc_nc_2706 goc_nc_2707 goc_nc_2708 goc_nc_2709 goc_nc_2710 goc_nc_2711 goc_nc_2712 goc_nc_2713 goc_nc_2714 goc_nc_2715 goc_nc_2716 goc_nc_2717 goc_nc_2718 goc_nc_2719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
