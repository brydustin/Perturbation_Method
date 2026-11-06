theory DCS_10_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_172: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 172) (-8)) (Float (int 172 + 1) (-8))"
  by eval

lemma dc_nc_172: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 172) (-8)) (Float (int 172 + 1) (-8))"
  by eval

lemma dc_c30_173: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 173) (-8)) (Float (int 173 + 1) (-8))"
  by eval

lemma dc_nc_173: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 173) (-8)) (Float (int 173 + 1) (-8))"
  by eval

lemma dc_c30_174: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 174) (-8)) (Float (int 174 + 1) (-8))"
  by eval

lemma dc_nc_174: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 174) (-8)) (Float (int 174 + 1) (-8))"
  by eval

lemma dc_c30_175: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 175) (-8)) (Float (int 175 + 1) (-8))"
  by eval

lemma dc_nc_175: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 175) (-8)) (Float (int 175 + 1) (-8))"
  by eval

end
