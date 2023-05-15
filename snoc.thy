theory snoc
  imports Complex_Main

begin
primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where
    "snoc [] a = [a]"
  | "snoc (x # xs) a = x # (snoc xs a)"

lemma snoc_append: "snoc xs a = xs @ [a]"
  apply (induct "xs")
  apply auto
done

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
  apply (induct "xs")
  apply (auto simp add:snoc_append)
done

end