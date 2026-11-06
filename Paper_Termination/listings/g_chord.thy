theorem chord_max:
  fixes f df ddf :: "real \<Rightarrow> real"
  assumes d1: "\<And>t. DERIV f t :> df t" and d2: "\<And>t. DERIV df t :> ddf t"
    and K: "\<And>t. \<bar>ddf t\<bar> \<le> K" and x: "a \<le> x" "x \<le> b"
  shows "f x \<le> max (f a) (f b) + K * (b - a)\<^sup>2 / 8"
