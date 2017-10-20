theory TestRevList
imports Main
begin

no_notation Nil("[]") and Cons (infixr "#" 65) and append (infixr "@" 65)
hide_type list
hide_const rev

datatype 'a list = Nil ("[]")
| Cons 'a "'a list" (infixr "#" 65)

primrec app :: "'a list => 'a list =>'a list" (infixr "@" 65)
where
"[] @ ys = ys" |
"(x # xs) @ ys = x # (xs @ ys)"

primrec rev :: "'a list => 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ (x #[])"

value "rev (True # False # [])"
value "rev (a # b# c# [])"

lemma app_assoc [simp]: "(xs @ys) @ zs = xs @(ys @zs)"
  apply(induct_tac xs)
  apply(auto)
  done

lemma app_Nil [simp]: "xs @ [] = xs"
  apply(induct_tac xs)
  apply(auto)
  done

lemma rev_app [simp]: "rev(xs@ys) = (rev ys) @ (rev xs)"
  apply(induct_tac xs)
   apply(auto)
  done

theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply(induct_tac xs)
  apply(auto)
done
