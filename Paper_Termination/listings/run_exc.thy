lemma run_exc: "run p N band tm ts t n = exc p N (c0 p t) (corrs p N band tm ts t n)"
  by (induction n) simp_all
