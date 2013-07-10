theory Scratch imports Main begin
theorem listprov: "length xs = length (rev xs)"
apply (induct xs) by auto


datatype 'a tree = Empty | tree 'a "'a tree" "'a tree"

fun length :: "'a tree \<Rightarrow> nat"
where
  "length Empty = 0"
 | "length (tree a x y) = 1 + length x + length y"

fun mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "mirror Empty = Empty"
| "mirror (tree a l r) = tree a (mirror r) (mirror l)"

theorem treeprov: "mirror (mirror t) = t"
using [[simp_trace=true]]
apply (induct t) by auto
print_statement tree.induct
end
