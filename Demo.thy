(*
  IMPORTANT: This file MUST be viewed with the Isabelle IDE.
    In a normal text editor, it is most likely unreadable!
    
    Download Isabelle at https://isabelle.in.tum.de/
   
*)
theory Demo
imports Main
begin

  section \<open>Functions\<close>
  subsection \<open>Append\<close>

  thm append.simps (* See result in output panel! *)
  
  value "[1::nat,2,3]@[4,5,6]" (* Use ::nat to indicate what number type you want! *)

  subsection \<open>Filter\<close>

  (* Erase elements not \<le>4 from list *)
  fun leq4 :: "nat list \<Rightarrow> nat list" where
    "leq4 [] = []"
  | "leq4 (x#l) = (if x\<le>4 then x # leq4 l else leq4 l)"  

  (*
    Function type:  nat list \<Rightarrow> nat list
      Function that takes a list argument, and returns a list
  
  *)
  
  
  
  value "leq4 [1,42,7,5,2,6,3]"

  (*
    Syntax for function application:
  
    f x\<^sub>1 x\<^sub>2 x\<^sub>3   function f applied to arguments x\<^sub>1 x\<^sub>2 x\<^sub>3
  *)
  
  
  
  (* More general: Erase elements not satisfying a condition *)
  term filter
  
  (* 'a list -- polymorphic type: Works for lists with any element type *)
  
  thm filter.simps
  value "filter (\<lambda>x. x\<le>4) [1::nat,42,7,5,2,6,3]"
  
  (*
    \<lambda>x.    define anonymous function, with parameter x
  *)
  
  
  (** BACK TO SLIDES **)
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  subsection \<open>Count\<close>

  (* How often does specific element occur in list? *)
  fun count :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
    "count [] y = 0"
  | "count (x#xs) y = (if x=y then 1 + count xs y else count xs y)"

  lemmas count_simps'[simp] = count.simps[abs_def] (* Technical detail, ignore for first! *)
  
  value "count [1,2,3,4,1,2,3,4,2,6] 2"

  
  subsection \<open>Sortedness Check\<close>
  (* Many possible definitions, a straightforward one is: *)
  term sorted
  thm sorted.simps(1) sorted1 sorted2

  value "sorted [1,2,2,3,4::nat]"  
  value "sorted [1,2,1,3,4::nat]"
  
  (** BACK TO SLIDES **)
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  subsection \<open>Quicksort\<close>
    
  fun qs :: "nat list \<Rightarrow> nat list" where
    "qs [] = []"
  | "qs (p#l) = qs (filter (\<lambda>x. x\<le>p) l) @ [p] @ qs (filter (\<lambda>x. x>p) l)"  
  
  
  value "qs [3,2,5,4,7]"

  
  (** BACK TO SLIDES **)  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

  section \<open>Correctness of Sorting Algorithm\<close>
  
  (* A sorting algorithm is correct, iff it returns a sorted list, with the same elements *)
  definition "correct_sorting f = (\<forall>xs. sorted (f xs) \<and> count (f xs) = count xs)"
  
  (*
    \<forall>xs.   for all xs
    \<and>      and
  *)
  
  (* Note: Two functions are equal, if they are equal for all arguments (extensionality).
  
    That is, count (f xs) = count xs means, that count is the same for all elements
  *)
  lemma "(count (f xs) = count xs) = (\<forall>x. count (f xs) x = count xs x)" 
    by auto
  
  (* Ultimately, we want to show *)
  lemma "correct_sorting qs"
    oops (* But this needs some preparation first! *)
  
  (** BACK TO SLIDES **)  
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
  section \<open>Proofs\<close>
  
  subsection \<open>Useful Properties\<close>
  
  lemma count_append: "count (l\<^sub>1@l\<^sub>2) x = count l\<^sub>1 x + count l\<^sub>2 x"
    by (induction l\<^sub>1) auto  (* Ignore the proofs for now *)
  
  lemma count_filter: "count (filter P l) x = (if P x then count l x else 0)"
    by (induction l) auto
  
  lemma count_filter_complete:
    "count (filter (\<lambda>x. x \<le> p) l) x + count (filter (\<lambda>x. x > p) l) x
     = count l x"
    by (cases "x\<le>p") (simp_all add: count_filter)
  
  (** BACK TO SLIDES **)  
  
    
    

  
  
  
      
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
  subsection \<open>Quicksort preserves Elements\<close>
  (* Let's prove preservation of elements first *)
  lemma qs_preserves_elements: "count (qs xs) = count xs"
  proof (induction xs rule: qs.induct)
    (* Proof principle: Show correctness, assuming recursive calls are correct *)
  
    case 1 (* Empty list *)
    show "count (qs []) = count []"
      apply (subst qs.simps) (* Definition of qs*)
      .. (* Trivial *)
      
  next
    case (2 p l) (* Non-empty list *)
    
    (* Assume the recursive calls preserve the elements *)
    assume 1: "count (qs (filter (\<lambda>x. x \<le> p) l)) = count (filter (\<lambda>x. x \<le> p) l)"
       and 2: "count (qs (filter (\<lambda>x. x > p) l)) = count (filter (\<lambda>x. x > p) l)"
    
    (* Show that this call preserves the elements *)   
    show "count (qs (p # l)) = count (p # l)" proof
      (* Extensionality: We show this per element *)
      fix x
      show "count (qs (p # l)) x = count (p # l) x" proof -
        have "count (qs (p # l)) x 
          = count (qs (filter (\<lambda>x. x \<le> p) l) @ [p] @ qs (filter (\<lambda>x. x > p) l)) x" 
          (* Definition of qs *)
          by simp
        also have "\<dots> = 
            count (qs (filter (\<lambda>x. x \<le> p) l)) x 
          + count [p] x 
          + count (qs (filter (\<lambda>x. x > p) l)) x"
          (* count_append *)
          by (simp add: count_append)
        also have "\<dots> =   
            count (filter (\<lambda>x. x \<le> p) l) x 
          + count [p] x 
          + count (filter (\<lambda>x. x > p) l) x"
          (* Assumptions for recursive calls *)
          by (simp add: 1 2)
        also have "\<dots> = 
            count [p] x 
          + (count (filter (\<lambda>x. x \<le> p) l) x 
             + count (filter (\<lambda>x. x > p) l) x)"
          (* Reordering *)
          by simp
        also have "\<dots> = count [p] x + count l x"
          (* count_filter_complete *)
          by (simp add: count_filter_complete)
        also have "\<dots> = count (p#l) x" 
          (* Def of count *)
          by simp
        finally show "count (qs (p # l)) x = count (p # l) x" .  
      qed
    qed
  qed          
  

  (* The above proof was quite explicit. 
    Many of the steps can be summarized 
    BUT: The proof is still the same!
      * It's more concise to write, but harder to understand!
      * Automation does not always work completely. 
        It requires training to get an intuition what will work and what won't,
        know some "tricks" to make things work,
        and to write proofs at a good balance of conciseness and readability!
      
  *)
  lemma "count (qs xs) = count xs"
    by (induction xs rule: qs.induct) 
       (auto simp: fun_eq_iff count_append count_filter_complete)
  
  (** BACK TO SLIDES **)  
       
       

  
  
  
  
  
         
       
       
       
       
       
       
       
       
       
       
       
       
       
       
       
  subsection \<open>More useful Properties\<close>
  
  (* Concept: Set of elements in list *)
  lemma in_set_conv_count: "x\<in>set l = (count l x > 0)"
    by (induction l) auto
  
  lemma qs_preserves_set: "set (qs l) = set l"
    by (auto simp: in_set_conv_count qs_preserves_elements)
    
  (* When is l\<^sub>1@l\<^sub>2 sorted ? 
    
    Both lists are sorted, and elements in l\<^sub>1 are less than elements in l\<^sub>2
  *)  
  thm sorted_append
  
  (* How about l\<^sub>1@[p]@l\<^sub>2 ? *)
  lemma sorted_lel: "sorted (l\<^sub>1@[p]@l\<^sub>2) = (
    sorted l\<^sub>1 \<and> sorted l\<^sub>2 \<and> (\<forall>x\<in>set l\<^sub>1. x\<le>p) \<and> (\<forall>x\<in>set l\<^sub>2. p\<le>x))"
    by (fastforce simp: sorted_append)

  (** BACK TO SLIDES **)  
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
  subsection \<open>Quicksort Sorts\<close>  
      
  lemma qs_sorts: "sorted (qs xs)"
  proof (induction xs rule: qs.induct)
    case 1 thus ?case by simp
  next
    case (2 p l)
    
    (* Introduce shortcut notation. Isabelle still sees expanded term, 
      it's just syntax sugar to make terms more concise to write! *)
    let ?qs1 = "qs (filter (\<lambda>x. x \<le> p) l)"
    let ?qs2 = "qs (filter (\<lambda>x. x > p) l)"
    
    (* Assume that recursive calls sort *)
    assume 1: "sorted ?qs1" and 2: "sorted ?qs2"
    
    (* Show that this call sorts *)
    show "sorted (qs (p#l))" proof -
      have "sorted (qs (p#l)) = sorted (?qs1 @ [p] @ ?qs2)"
       (* Def. of qs *)
        by simp
      also have "\<dots> 
        = (sorted ?qs1 \<and> sorted ?qs2 \<and> (\<forall>x\<in>set ?qs1. x\<le>p) \<and> (\<forall>x\<in>set ?qs2. p\<le>x))"
        (* sorted_lel *)
        by (simp add: sorted_lel[simplified])
      also have "\<dots> = ((\<forall>x\<in>set ?qs1. x\<le>p) \<and> (\<forall>x\<in>set ?qs2. p\<le>x))" 
        (* Assumption that recursive calls sort! *)
        by (simp add: 1 2)
      also have "\<dots>" proof
        (* It remains to show that "set ?qs1" is \<le> pivot, and "set qs2" \<ge> pivot *)
        have "set ?qs1 = set (filter (\<lambda>x. x \<le> p) l)" by (simp add: qs_preserves_set)
          (* Set of elements preserved by qs *)
        also have "\<dots> = {x \<in> set l. x\<le>p}" by simp
          (* Elements of filtered list are elements of original list that satisfy condition *)
        also have "\<forall>x\<in>{x \<in> set l. x\<le>p}. x\<le>p" by auto
        finally show "\<forall>x\<in>set ?qs1. x\<le>p" .
        
        show "\<forall>x\<in>set ?qs2. x\<ge>p" by (auto simp: qs_preserves_set) 
          (* Other direction: analogously. Done more concisely here. *)
      qed  
      finally show "sorted (qs (p # l))" by auto
    qed
  qed    
    
    
  (* Again, proof can be written down very concise 
    (but hard to understand what is going on for the beginner!)*)
  lemma "sorted (qs xs)"
    by (induction xs rule: qs.induct)
       (auto simp: sorted_append qs_preserves_set)
  
  subsection \<open>Quicksort is correct Sorting Algorithm\<close>
  (* Finally! *)    
  theorem qs_correct: "correct_sorting qs"
    unfolding correct_sorting_def
    using qs_preserves_elements qs_sorts 
    by simp

end
