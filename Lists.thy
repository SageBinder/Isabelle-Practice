theory Lists
  imports Main

begin

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace x y [] = []"
  | "replace x y (z # zs) = (if z = x then y else z) # replace x y zs"

lemma rev_append: "rev (a # zs) = (rev zs) @ [a]"
proof(induct zs)
  case Nil
  show ?case by auto
next
  case (Cons a zs)
  show ?case by auto
qed

lemma repl_append: "replace x y (zs @ a) = (replace x y zs) @ (replace x y a)"
proof(induct zs)
  case Nil
  show ?case by auto
next
  case (Cons z zs)
  fix a
  assume IH: "replace x y (zs @ a) = replace x y zs @ replace x y a"
  define cons_app where "cons_app \<equiv> (z # zs) @ a"
  hence "cons_app = z # (zs @ a)" using cons_app_def by auto
  hence "replace x y cons_app = (replace x y [z]) @ (replace x y (zs @ a))" by auto
  hence "replace x y cons_app = (replace x y [z]) @ (replace x y zs) @ (replace x y a)" using IH by auto
  hence "replace x y cons_app = (replace x y (z # zs)) @ (replace x y a)" by auto
  thus "replace x y ((z # zs) @ a) = replace x y (z # zs) @ replace x y a" using cons_app_def by auto
qed

theorem "rev(replace x y zs) = replace x y (rev zs)"
proof(induct zs)
  case Nil
  show ?case by auto
next
  case (Cons z zs)
  fix z zs
  assume IH: "rev (replace x y zs) = replace x y (rev zs)"
  define repl_rev where "repl_rev \<equiv> replace x y (rev (z # zs))"
  have "repl_rev = replace x y ((rev zs) @ [z])" using rev_append repl_rev_def by auto
  hence "repl_rev = replace x y (rev zs) @ replace x y [z]"
    using repl_append[of "x" "y" "(rev zs)" "[z]"] by auto
  hence "repl_rev = rev (replace x y zs) @ replace x y [z]" using IH by auto
  hence "repl_rev = rev (replace x y (z # zs))" using rev_append by auto
  thus "rev (replace x y (z # zs)) = replace x y (rev (z # zs))" using repl_rev_def by auto
qed
end
