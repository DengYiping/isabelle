theory poly
  imports Main HOL
begin

primrec pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"pow x 0 = Suc 0"
| "pow x (Suc y) = x * pow x y"

lemma add_rule: "pow x (y + z) = pow x y * pow x z"
  apply(induct z)
   apply auto
  done

datatype poly = Nat nat | Var nat | Plus poly poly | Times poly poly

primrec pval :: "poly \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
"pval (Nat n) _ = n"
| "pval (Var v) f = f v"
| "pval (Plus p q) f = (pval p f) + (pval p f)"
| "pval (Times p q) f = (pval p f) * (pval p f)"