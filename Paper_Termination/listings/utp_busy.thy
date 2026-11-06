lemma busy_less:
  assumes "stops_within p N band tm ts t D"
    and "elig p N band tm (run p N band tm ts t n) t \<noteq> {}"
  shows "n < D"
