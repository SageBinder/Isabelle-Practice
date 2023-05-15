theory quant
imports Main

begin

fun replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "replace _ _ [] = []"
  | "replace a b (x # xs) = (if x = a then b else x) # replace a b xs"


lemma replace_append: "replace x y (xs @ ys) = (replace x y xs) @ (replace x y ys)"
  apply (induct "xs")
  apply (auto)
done

theorem "rev (replace x y zs) = replace x y (rev zs)"
  apply (induction "zs")
  apply (simp)
  apply (auto simp add:replace_append)
done

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
  quickcheck

theorem "replace y z (replace x y zs) = replace x z zs"
  quickcheck

end