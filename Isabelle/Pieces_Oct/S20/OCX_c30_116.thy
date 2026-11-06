theory OCX_c30_116
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1856: "oc_sub oc_b30 1856"
  by (oc_eval oc_c30_1856)

lemma oc_c30_1857: "oc_sub oc_b30 1857"
  by (oc_eval oc_c30_1857)

lemma oc_c30_1858: "oc_sub oc_b30 1858"
  by (oc_eval oc_c30_1858)

lemma oc_c30_1859: "oc_sub oc_b30 1859"
  by (oc_eval oc_c30_1859)

lemma oc_c30_1860: "oc_sub oc_b30 1860"
  by (oc_eval oc_c30_1860)

lemma oc_c30_1861: "oc_sub oc_b30 1861"
  by (oc_eval oc_c30_1861)

lemma oc_c30_1862: "oc_sub oc_b30 1862"
  by (oc_eval oc_c30_1862)

lemma oc_c30_1863: "oc_sub oc_b30 1863"
  by (oc_eval oc_c30_1863)

lemma oc_c30_1864: "oc_sub oc_b30 1864"
  by (oc_eval oc_c30_1864)

lemma oc_c30_1865: "oc_sub oc_b30 1865"
  by (oc_eval oc_c30_1865)

lemma oc_c30_1866: "oc_sub oc_b30 1866"
  by (oc_eval oc_c30_1866)

lemma oc_c30_1867: "oc_sub oc_b30 1867"
  by (oc_eval oc_c30_1867)

lemma oc_c30_1868: "oc_sub oc_b30 1868"
  by (oc_eval oc_c30_1868)

lemma oc_c30_1869: "oc_sub oc_b30 1869"
  by (oc_eval oc_c30_1869)

lemma oc_c30_1870: "oc_sub oc_b30 1870"
  by (oc_eval oc_c30_1870)

lemma oc_c30_1871: "oc_sub oc_b30 1871"
  by (oc_eval oc_c30_1871)

lemma upt_c30_116: "[1856..<1872] = [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]"
  by (simp add: upt_rec)

lemma sec_c30_116: "\<forall>j\<in>{16 * 116..<16 * 116 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 116..<16 * 116 + 16}"
  then have "j \<in> set [1856..<1872]" unfolding set_upt by simp
  then have "j \<in> set [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]" unfolding upt_c30_116 .
  then show "oc_sub oc_b30 j" using oc_c30_1856 oc_c30_1857 oc_c30_1858 oc_c30_1859 oc_c30_1860 oc_c30_1861 oc_c30_1862 oc_c30_1863 oc_c30_1864 oc_c30_1865 oc_c30_1866 oc_c30_1867 oc_c30_1868 oc_c30_1869 oc_c30_1870 oc_c30_1871
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
