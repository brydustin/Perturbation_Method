lemma patt_exc_rows: "patt p N (exc p N c \<sigma>) (grid m) = (\<Sum>j<N. rows p N \<sigma> m j * c j)"
