theory GDCX_nc_169
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2704: "gdc_sub None 2704"
  by (gdc_eval gdc_nc_2704)

lemma gdc_nc_2705: "gdc_sub None 2705"
  by (gdc_eval gdc_nc_2705)

lemma gdc_nc_2706: "gdc_sub None 2706"
  by (gdc_eval gdc_nc_2706)

lemma gdc_nc_2707: "gdc_sub None 2707"
  by (gdc_eval gdc_nc_2707)

lemma gdc_nc_2708: "gdc_sub None 2708"
  by (gdc_eval gdc_nc_2708)

lemma gdc_nc_2709: "gdc_sub None 2709"
  by (gdc_eval gdc_nc_2709)

lemma gdc_nc_2710: "gdc_sub None 2710"
  by (gdc_eval gdc_nc_2710)

lemma gdc_nc_2711: "gdc_sub None 2711"
  by (gdc_eval gdc_nc_2711)

lemma gdc_nc_2712: "gdc_sub None 2712"
  by (gdc_eval gdc_nc_2712)

lemma gdc_nc_2713: "gdc_sub None 2713"
  by (gdc_eval gdc_nc_2713)

lemma gdc_nc_2714: "gdc_sub None 2714"
  by (gdc_eval gdc_nc_2714)

lemma gdc_nc_2715: "gdc_sub None 2715"
  by (gdc_eval gdc_nc_2715)

lemma gdc_nc_2716: "gdc_sub None 2716"
  by (gdc_eval gdc_nc_2716)

lemma gdc_nc_2717: "gdc_sub None 2717"
  by (gdc_eval gdc_nc_2717)

lemma gdc_nc_2718: "gdc_sub None 2718"
  by (gdc_eval gdc_nc_2718)

lemma gdc_nc_2719: "gdc_sub None 2719"
  by (gdc_eval gdc_nc_2719)

lemma gupt_nc_169: "[2704..<2720] = [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]"
  by (simp add: upt_rec)

lemma gsec_nc_169: "\<forall>j\<in>{16 * 169..<16 * 169 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 169..<16 * 169 + 16}"
  then have "j \<in> set [2704..<2720]" unfolding set_upt by simp
  then have "j \<in> set [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]" unfolding gupt_nc_169 .
  then show "gdc_sub None j" using gdc_nc_2704 gdc_nc_2705 gdc_nc_2706 gdc_nc_2707 gdc_nc_2708 gdc_nc_2709 gdc_nc_2710 gdc_nc_2711 gdc_nc_2712 gdc_nc_2713 gdc_nc_2714 gdc_nc_2715 gdc_nc_2716 gdc_nc_2717 gdc_nc_2718 gdc_nc_2719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
