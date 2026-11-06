theory OCX_nc_116
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1856: "oc_sub None 1856"
  by (oc_eval oc_nc_1856)

lemma oc_nc_1857: "oc_sub None 1857"
  by (oc_eval oc_nc_1857)

lemma oc_nc_1858: "oc_sub None 1858"
  by (oc_eval oc_nc_1858)

lemma oc_nc_1859: "oc_sub None 1859"
  by (oc_eval oc_nc_1859)

lemma oc_nc_1860: "oc_sub None 1860"
  by (oc_eval oc_nc_1860)

lemma oc_nc_1861: "oc_sub None 1861"
  by (oc_eval oc_nc_1861)

lemma oc_nc_1862: "oc_sub None 1862"
  by (oc_eval oc_nc_1862)

lemma oc_nc_1863: "oc_sub None 1863"
  by (oc_eval oc_nc_1863)

lemma oc_nc_1864: "oc_sub None 1864"
  by (oc_eval oc_nc_1864)

lemma oc_nc_1865: "oc_sub None 1865"
  by (oc_eval oc_nc_1865)

lemma oc_nc_1866: "oc_sub None 1866"
  by (oc_eval oc_nc_1866)

lemma oc_nc_1867: "oc_sub None 1867"
  by (oc_eval oc_nc_1867)

lemma oc_nc_1868: "oc_sub None 1868"
  by (oc_eval oc_nc_1868)

lemma oc_nc_1869: "oc_sub None 1869"
  by (oc_eval oc_nc_1869)

lemma oc_nc_1870: "oc_sub None 1870"
  by (oc_eval oc_nc_1870)

lemma oc_nc_1871: "oc_sub None 1871"
  by (oc_eval oc_nc_1871)

lemma upt_nc_116: "[1856..<1872] = [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]"
  by (simp add: upt_rec)

lemma sec_nc_116: "\<forall>j\<in>{16 * 116..<16 * 116 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 116..<16 * 116 + 16}"
  then have "j \<in> set [1856..<1872]" unfolding set_upt by simp
  then have "j \<in> set [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]" unfolding upt_nc_116 .
  then show "oc_sub None j" using oc_nc_1856 oc_nc_1857 oc_nc_1858 oc_nc_1859 oc_nc_1860 oc_nc_1861 oc_nc_1862 oc_nc_1863 oc_nc_1864 oc_nc_1865 oc_nc_1866 oc_nc_1867 oc_nc_1868 oc_nc_1869 oc_nc_1870 oc_nc_1871
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
