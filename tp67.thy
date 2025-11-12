theory tp67
imports Main  "~~/src/HOL/Library/Code_Target_Int" 
begin

(* Types des expressions, conditions et programmes (statement) *)

datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip

(* type des expressions static et méthodes utilitaires sur ce type *)

datatype staticValue =  Undefine | Value int | Either int int 

fun staticAdd::"staticValue \<Rightarrow> staticValue \<Rightarrow> staticValue"
  where
"staticAdd Undefine _ = Undefine" |
"staticAdd _ Undefine = Undefine" |
"staticAdd (Value x) (Value y) = Value(x+y)" |
"staticAdd (Either x y) (Value z) = Either (x+z) (y+z)" |
"staticAdd (Value x) (Either y z) = Either (x+y) (x+z)" |
"staticAdd (Either x y) (Either z t) = Undefine"

fun staticSub::"staticValue \<Rightarrow> staticValue \<Rightarrow> staticValue"
  where
"staticSub Undefine _ = Undefine" |
"staticSub _ Undefine = Undefine" |
"staticSub (Value x) (Value y) = Value(x-y)" |
"staticSub (Either x y) (Value z) = Either (x-z) (y-z)" |
"staticSub (Value x) (Either y z) = Either (x-y) (x-z)" |
"staticSub (Either x y) (Either z t) = Undefine"

(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"


(* Des exemples de programmes *)

(* p1= exec(0) *)
definition "p1= Exec (Constant 0)"

(* p2= {
        print(10)
        exec(0+0)
       }
*)

definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)

definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print et le type static correspondant *)
datatype event= X int | P int

datatype staticEvent = SX staticValue | SP staticValue

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"
definition "(st1::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)

(* les  types des flux de sortie, d'entree et les tables de symboles statics *)

type_synonym staticOutchan= "staticEvent list"
definition "staticel1= [SX (Value 1), SP (Value 10), SX (Value 0), SP Undefine]"

type_synonym staticSymTable = "(string * staticValue) list"
definition "(staticst1::staticSymTable)= [(''x'', (Value 10)),(''y'', Undefine)]"

(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)

(* méthodes utilitaires sur les tables de symboles statics *)

fun cleanTable::"staticSymTable => staticSymTable"
  where
"cleanTable [] = []" |
"cleanTable ((x, e)#xs) = ( (x, Undefine)#(cleanTable xs) )"

fun cleanSection::"staticSymTable => staticSymTable => staticSymTable"
  where
"cleanSection t1 t = ( let sectionSize = (length t1) - (length t) in cleanTable (take sectionSize t1) )"

fun getSection::"staticSymTable \<Rightarrow> staticSymTable \<Rightarrow> staticSymTable"
  where
"getSection t1 t = ( let sectionSize = (length t1) - (length t) in (take sectionSize t1) )"

(* fusionne les tables de symboles static de blocs d'éxécutions disjoints *)
fun joinTables::"staticSymTable \<Rightarrow> staticSymTable \<Rightarrow> staticSymTable"
  where
"joinTables [] ys = (cleanTable ys)" |
"joinTables ((x, Undefine)#xs) ys = ( (x, Undefine)#(joinTables xs ys) )" |
"joinTables ((x, (Value e))#xs) ys = ( case (assoc x ys) of Some (Value y) \<Rightarrow> (
                                if e = y then ( (x, (Value e))#(joinTables xs ys) )
                                         else ( (x, (Either e y))#(joinTables xs ys) ) ) |
                                None \<Rightarrow> (x, Undefine)#(joinTables xs ys) |
                                Some (Either a b) \<Rightarrow> (x, Undefine)#(joinTables xs ys) |
                                Some Undefine \<Rightarrow> (x, Undefine)#(joinTables xs ys)
)" |
"joinTables ((x, Either a b)#xs) ys = (x, Undefine)#(joinTables xs ys)"

(* Evaluation des expressions par rapport a une table de symboles *)

fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

fun staticEvalE:: "expression \<Rightarrow> staticSymTable \<Rightarrow> staticValue"
  where
"staticEvalE (Constant s) e = Value s" |
"staticEvalE (Variable s) e = (case (assoc s e) of None \<Rightarrow> (Value (-1)) | Some(y) \<Rightarrow> y)" |
"staticEvalE (Sum e1 e2) e = staticAdd (staticEvalE e1 e) (staticEvalE e2 e)" |
"staticEvalE (Sub (Variable x) (Variable y)) e = (if x = y then
                                   (Value 0) else 
                                   (staticSub (staticEvalE (Variable x) e) (staticEvalE (Variable y) e) )
)" |
"staticEvalE (Sub e1 e2) e = staticSub (staticEvalE e1 e) (staticEvalE e2 e)"

(* Exemple d'évaluation d'expression *)

value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"

fun staticEqual::"staticValue \<Rightarrow> staticValue \<Rightarrow> bool option"
  where
"staticEqual (Value x) (Value y) = Some( (x=y) )" |
"staticEqual e1 e2 = None"

fun staticEvalC:: "condition \<Rightarrow> staticSymTable \<Rightarrow> bool tp67.option"
  where
"staticEvalC (Eq (Variable x) (Variable y)) t = ( if x = y then (Some True) else
                                    ( staticEqual (staticEvalE (Variable x) t) (staticEvalE (Variable y) t) )
 )" |
"staticEvalC (Eq e1 e2) t = ( staticEqual (staticEvalE e1 t) (staticEvalE e2 t) )"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"

fun staticEvalS::"statement \<Rightarrow> (staticSymTable * staticOutchan) \<Rightarrow> (staticSymTable * staticOutchan)"
  where
"staticEvalS Skip x = x" |
"staticEvalS (Aff s e) (t,outch) = ( ( ( (s, staticEvalE e t)#t ), outch )  )" |
"staticEvalS (If c s1 s2)  (t,outch) = ( case(staticEvalC c t) of
                              Some b \<Rightarrow> if b then (staticEvalS s1 (t,outch)) else (staticEvalS s2 (t,outch)) |
                              None \<Rightarrow> let (t1, outch1) = (staticEvalS s1 (t,outch)) in (
                                let (t2, outch2) = (staticEvalS s2 (t,outch)) in (
                                  ( (joinTables (getSection t1 t) (getSection t2 t)) @ t , outch1 @ outch2)
                                )
                              )

 )" |
"staticEvalS (Seq s1 s2) (t,outch)= 
    (let (t2,outch2)= (staticEvalS s1 (t,outch)) in
        staticEvalS s2 (t2,outch2))" |
"staticEvalS (Read s) (t,outch) = ( ( (s, Undefine)#t ), outch )" |
"staticEvalS (Print e) (t,outch)= (t,((SP (staticEvalE e t))#outch))" |
"staticEvalS (Exec e) (t,outch)= 
  (let res = staticEvalE e t in
   (t,((SX res)#outch)))"

value "staticEvalS p1 ([], [])"

(* Exemples d'évaluation de programmes *)
(* Les programmes p1, p2, p3, p4 ont été définis plus haut *)
(* p1= exec(0) *)

value "evalS p1 ([],[],[])"

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])"

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])"

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))"
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "bad9= (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 2))) (If (Eq (Variable ''x'') (Variable ''z'')) (Exec (Constant 1)) (Exec (Constant 0))))))"

definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"
definition "ok15= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok16= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Sum (Variable ''y'') (Variable ''x''))) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok17= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Constant 10) (Sub (Sum (Variable ''x'') (Variable ''y'')) (Constant 3))) (Sub (Sum (Variable ''y'') (Variable ''x'')) (Sub (Variable ''x'') (Sum (Variable ''x'') (Constant 7))))) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"

(* Le TP commence ici! *)
(* TODO: BAD, san0, lemme de correction *)

(* Indique si le résultat de l'éxécution d'un programme éxécute du code dangereux *)
fun BAD::"(symTable * inchan * outchan) \<Rightarrow>  bool"
  where
"BAD (t, inch, []) = False" |
"BAD (t, inch, (X e)#outch) = (e=0 \<or> (BAD (t, inch, outch)))" |
"BAD (t, inch, (P e)#outch) = (BAD (t, inch, outch))"

(* Indique si le résultat de l'éxécution static du programme éxécute du code dangereux *)
fun staticBAD::"staticSymTable * staticOutchan \<Rightarrow> bool"
  where
"staticBAD (t, []) = False" |
"staticBAD (t, (SX (Undefine))#outch) = True" |
"staticBAD (t, (SX (Value e))#outch) = (e=0 \<or> (staticBAD (t, outch)))" |
"staticBAD (t, (SX (Either x y))#outch) = (x=0 \<or> y=0 \<or> (staticBAD (t, outch)))" |
"staticBAD (t, (SP e)#outch) = (staticBAD (t, outch))"

(* refuse les programmes qui contiennent une instruction Exec *)
fun san0::"statement \<Rightarrow> bool"
  where
"san0 (Seq s1 s2) = ((san0 s1) \<and> (san0 s2))" |
"san0 (If c s1 s2) = ((san0 s1) \<and> (san0 s2))" |
"san0 (Exec e) = False" |
"san0 statement = True"

   
(* Accepte des programmes contenant seulement des instructions Exec appellées sur des constantes différentes de 0 *)
fun san1::"statement \<Rightarrow> bool"
  where
"san1 (Seq s1 s2) = ((san1 s1) \<and> (san1 s2))" |
"san1 (If c s1 s2) = ((san1 s1) \<and> (san1 s2))" |
"san1 (Exec (Constant x)) = (x \<noteq> 0)" |
"san1 (Exec expr) = False" |
"san1 statement = True"


(* Accepte des programmes contenant seulement des instructions Exec appellées sur des constantes différentes de 0
   ou des opérations sur des constantes dont le résultat est différent de 0 *)
fun san2::"statement \<Rightarrow> bool"
  where
"san2 (Seq s1 s2) = ((san2 s1) \<and> (san2 s2))" |
"san2 (If c s1 s2) = ((san2 s1) \<and> (san2 s2))" |
"san2 (Exec (Constant x)) = (x \<noteq> 0)" |
"san2 (Exec (Sum (Constant x) (Constant y))) = (x+y \<noteq> 0)" |
"san2 (Exec (Sub (Constant x) (Constant y))) = (x-y \<noteq> 0)" |
"san2 (Exec expr) = False" |
"san2 statement = True"

(* Accepte des programmes contenant seulement des instructions Exec appellées sur des constantes différentes de 0
   ou des opérations sur des constantes dont le résultat est différent de 0 en ignorant les blocs trivialements 
   non parcourus *)
fun san3::"statement \<Rightarrow> bool"
  where
"san3 (Seq s1 s2) = ((san3 s1) \<and> (san3 s2))" |
"san3 (If ( Eq (Constant x) (Constant y) ) s1 s2) = ( if (x = y) then (san3 s1) else (san3 s2) )" |
"san3 (If c s1 s2) = ((san3 s1) \<and> (san3 s2))" |
"san3 (Exec (Constant x)) = (x \<noteq> 0)" |
"san3 (Exec (Sum (Constant x) (Constant y))) = (x+y \<noteq> 0)" |
"san3 (Exec (Sub (Constant x) (Constant y))) = (x-y \<noteq> 0)" |
"san3 (Exec expr) = False" |
"san3 statement = True"

(* Accepte des programmes dont l'évaluation static n'indique pas l'éxécution de code dangereux *)
fun san4::"statement \<Rightarrow> bool"
  where
"san4 statement = (\<not>(staticBAD (staticEvalS statement ([], []))))"

(* choisit la version de san qu'on veut utiliser pour éécuter les tests suivants *)
definition "chosensan = san4"

lemma "(BAD (evalS p (t, inch, []))) \<longrightarrow> (\<not>(chosensan p))"
  (* nitpick[timeout=120] *)
  (* quickcheck[tester=narrowing,size=5,timeout=120] *)
  sorry


value "evalS (Exec (Sub (Variable ''s'') (Variable ''s''))) ([]::symTable, []::inchan, []::outchan)"
value "staticEvalS (Read ''v1'') ([]::staticSymTable, []::staticOutchan)"
value "staticEvalS ( Seq (Read ''v1'') (Exec (Variable ''v1'')) ) ([]::staticSymTable, []::staticOutchan)"
value "staticBAD ([(''v1'', Undefine)], [SX Undefine])"

value "chosensan ok0" 
value "chosensan ok1"
value "chosensan ok2"
value "chosensan ok3"
value "chosensan ok4"
value "chosensan ok5"
value "chosensan ok6"
value "chosensan ok7"
value "chosensan ok8"
value "chosensan ok9"
value "chosensan ok10"
value "chosensan ok11"
value "chosensan ok12"
value "chosensan ok13"

value "chosensan bad1"
value "chosensan bad2"
value "chosensan bad3"
value "chosensan bad4"
value "chosensan bad5"
value "chosensan bad6"
value "chosensan bad7"
value "chosensan bad8"
value "chosensan bad9"

(* Si san accepte un programme alors son évaluation, quelles que soient les entrées utilisateur (inchan)
   ne provoquera pas d'exec(0) *)

lemma correction: "(BAD (evalS p ([], inch, []))) \<longrightarrow> (\<not>(san4 p))"
  (* nitpick[timeout=120] *)
  (* quickcheck[tester=narrowing,size=5,timeout=120] *)
  sorry


(* ----- Restriction de l'export Scala (Isabelle 2023) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2023) *)
code_reserved Scala
  expression condition statement 
code_printing
   type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 
\<open>// Code generated by Isabelle
package tp67

import utilities.Datatype._
// automatic conversion of utilities.Datatype.Int.int to Int.int
object AutomaticConversion {
  implicit def int2int(i: utilities.Datatype.Int.int): Int.int =
    i match {
      case utilities.Datatype.Int.int_of_integer(i) => Int.int_of_integer(i)
    }

  def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
    (if (k == BigInt(0)) (BigInt(0), false)
     else {
       val (r, s): (BigInt, BigInt) =
         (
             (k: BigInt) =>
               (l: BigInt) =>
                 if (l == 0) (BigInt(0), k)
                 else
                   (k.abs /% l.abs)
         ).apply(k).apply(BigInt(2));
       ((if (BigInt(0) < k) r else (-r) - s), s == BigInt(1))
     })

  def char_of_integer(k: BigInt): Str.char = {
    val (q0, b0): (BigInt, Boolean) = bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = bit_cut_integer(q5)
    val a: (BigInt, Boolean) = bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    Str.Chara(b0, b1, b2, b3, b4, b5, b6, aa)
  }

  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil)     => Nil
    case (f, x :: xs) => f(x) :: map[A, B](f, xs)
  }

  def explodeList(l: List[Char]): List[Str.char] = {
    (l.map(c => {
      val k: Int = c.toInt;
      if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal")
    }))
      .map(a => char_of_integer(a))
  }

  def explode(s: String): List[Str.char] = {
    explodeList(s.toCharArray.toList)
  }

  // conversion from Scala String to HOL string
  implicit def string2charList(s: String): List[Str.char] = explode(s)

  // conversion from Scala List[Char] to HOL List[Str.char]
  implicit def charList2charList(l: List[Char]): List[Str.char] =
    explodeList(l)
  // conversion of a pair with a Scala List[String] on the first position
  // to an HOL pair with an HOL List[Str.char] on first position
  implicit def tupleString2tupleString[T](
      t: (List[Char], T)
  ): (List[Str.char], T) = t match {
    case (e1, e2) => (charList2charList(e1), e2)
  }

  // conversion from Isabelle Int.int to Project Int.int
  implicit def int2dataint(i: Int.int): utilities.Datatype.Int.int =
    i match {
      case Int.int_of_integer(i) => utilities.Datatype.Int.int_of_integer(i)
    }

  def stringChar2char(x: Str.char): Char = {
    x match {
      case Str.Chara(x1, x2, x3, x4, x5, x6, x7, x8) => {
        var n = 0;
        n = if (x8) 2 * n + 1 else 2 * n;
        n = if (x7) 2 * n + 1 else 2 * n;
        n = if (x6) 2 * n + 1 else 2 * n;
        n = if (x5) 2 * n + 1 else 2 * n;
        n = if (x4) 2 * n + 1 else 2 * n;
        n = if (x3) 2 * n + 1 else 2 * n;
        n = if (x2) 2 * n + 1 else 2 * n;
        n = if (x1) 2 * n + 1 else 2 * n;
        n.toChar
      }
    }
  }

  // conversion from Isabelle String to Lists of Chars
  implicit def charList2String(l: List[Str.char]): List[Char] = {
    l.map(stringChar2char(_))
  }
}

import AutomaticConversion._
\<close>


(* Directive pour l'exportation de l'analyseur *)

(* J'ai enlevé le code entre () avant file,
   n'injecter que l'objet tp67 du code généré pour éviter les erreurs de syntaxes *)
export_code chosensan in Scala file "~/Master1-IL/ACF/TP-67/san.scala"

(* à adapter en fonction du chemin de votre projet TP67 *)

end
