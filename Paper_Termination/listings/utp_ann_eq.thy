lemma perturb_ann_is_perturb: "perturb_ann (p, N, band, tm, ts, t, D) = perturb (p, N, band, tm, ts, t)"
  by (simp add: perturb_ann_def perturb_def while_inv_var_def)
