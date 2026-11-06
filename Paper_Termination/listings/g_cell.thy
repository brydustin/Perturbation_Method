theorem pw_cell_max:
  assumes "a \<le> x" "x \<le> b"
  shows "pw p N c x \<le> max (pw p N c a) (pw p N c b) + Hc c p N * (b - a)\<^sup>2 / 8"
