theory DCS_10_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_168: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 168) (-8)) (Float (int 168 + 1) (-8))"
  by eval

lemma dc_nc_168: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 168) (-8)) (Float (int 168 + 1) (-8))"
  by eval

lemma dc_c30_169: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 169) (-8)) (Float (int 169 + 1) (-8))"
  by eval

lemma dc_nc_169: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 169) (-8)) (Float (int 169 + 1) (-8))"
  by eval

lemma dc_c30_170: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 170) (-8)) (Float (int 170 + 1) (-8))"
  by eval

lemma dc_nc_170: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 170) (-8)) (Float (int 170 + 1) (-8))"
  by eval

lemma dc_c30_171: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 171) (-8)) (Float (int 171 + 1) (-8))"
  by eval

lemma dc_nc_171: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 171) (-8)) (Float (int 171 + 1) (-8))"
  by eval

end
