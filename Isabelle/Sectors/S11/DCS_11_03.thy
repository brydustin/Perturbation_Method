theory DCS_11_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_188: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 188) (-8)) (Float (int 188 + 1) (-8))"
  by eval

lemma dc_nc_188: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 188) (-8)) (Float (int 188 + 1) (-8))"
  by eval

lemma dc_c30_189: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 189) (-8)) (Float (int 189 + 1) (-8))"
  by eval

lemma dc_nc_189: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 189) (-8)) (Float (int 189 + 1) (-8))"
  by eval

lemma dc_c30_190: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 190) (-8)) (Float (int 190 + 1) (-8))"
  by eval

lemma dc_nc_190: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 190) (-8)) (Float (int 190 + 1) (-8))"
  by eval

lemma dc_c30_191: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 191) (-8)) (Float (int 191 + 1) (-8))"
  by eval

lemma dc_nc_191: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 191) (-8)) (Float (int 191 + 1) (-8))"
  by eval

end
