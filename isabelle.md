# Isabelle

## What is Isabelle
 - Iteractive theorem prover, written in Standard ML
 - a generic system used as a specification and verification system and for implementing logical formalisms
 - Isar is the proof language that structures the proof written to look like a human readable proof.
 - Isabelle is used widely in the Industry like in the design of HP 9000 servers

## HOL
 - Stards for Higher Order Logic, used for expressing theorems in Isabelle
 - HOL = Functional Programming + LOgic

## Example
 - Isabelle file name should be the same as the theory name
 - Example of proofing a list
 - `Main` stands for main theorem, contains all the basic theorem we might need( natural numbers, sets, ...)
 - `no_notation` removes the specified syntax annotation from the present context.
 - `infixr` means the operator is right associative, and 65 is the precedence level
 - `hide_type list` hide the type contains list
 - `app` appends a element to a list
 - `rev` gives you the reverse of a list
 - `value` just evaluate the result
```
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
"(x #xs) @ ys = x# (xs @ys)"

primrec rev :: "'a list => 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ (x #[])"

value "rev (True # False # [])"
value "rev (a # b# c# [])"
```

Isabelle need to prove its correctness.
Prove reverse of reverse is itself.
1. First, write down the theorem
2. Write down the lemma to help it

```
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
```

## Another Example

