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
  fun f :: "nat \<Rightarrow> nat" where "f x = (if x<65 then f (x+1) else 8)"
  *)
  
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
  
  value "filter (\<lambda>s::string. size s < 3) [''a'',''abcd'',''ab'']"
  
  value "CHR ''a''"
  
  
  
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
  thm sorted.simps
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
  lemma qs_preserves_elements: "count (qs xs) x = count xs x"
  proof (induction xs rule: qs.induct)
    (* Proof principle: Show correctness, assuming recursive calls are correct *)
  
    case 1 (* Empty list *)
    show "count (qs []) x = count [] x"
      apply (subst qs.simps) (* Definition of qs*)
      .. (* reflexivity *)
      
  next
    case (2 p l) (* Non-empty list *)
    
    let ?l\<^sub>1 = "filter (\<lambda>x. x \<le> p) l"
    let ?l\<^sub>2 = "filter (\<lambda>x. x > p) l"
    
    (* Assume the recursive calls preserve the elements *)
    assume IH1: "count (qs ?l\<^sub>1) x = count ?l\<^sub>1 x"
       and IH2: "count (qs ?l\<^sub>2) x = count ?l\<^sub>2 x"
    
    (* Show that this call preserves the elements *)   
    show "count (qs (p # l)) x = count (p # l) x" proof -
      have "count (qs (p # l)) x = count (qs ?l\<^sub>1 @ [p] @ qs ?l\<^sub>2) x" 
        by simp (* Def. of qs *)
      also have "\<dots> = count [p] x + count (qs ?l\<^sub>1) x + count (qs ?l\<^sub>2) x"
        by (simp add: count_append) (* count_append, commutativity of + *)
      also have "\<dots> = count [p] x + (count (?l\<^sub>1) x + count (?l\<^sub>2) x)"
        by (simp add: IH1 IH2) (* Induction hypothesis *)
      also have "\<dots> = count [p] x + count l x"
        by (simp add: count_filter_complete) (* count_filter_complete *)
      also have "\<dots> = count (p#l) x" 
        by simp (* Def of count *)
      finally show "count (qs (p # l)) x = count (p # l) x" .  
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
  lemma "count (qs xs) x = count xs x"
    by (induction xs rule: qs.induct) 
       (auto simp: count_append count_filter_complete)
  
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

    
  lemma in_set_filter: "x\<in>set (filter P xs) \<Longrightarrow> P x" by simp 
    (* A \<Longrightarrow> B   if A holds then B holds *)
    
  lemma "x\<in>set (filter P xs) = (P x \<and> x\<in>set xs)"
    by auto
    
    
  subsection \<open>Quicksort Sorts\<close>  
      
  lemma qs_sorts: "sorted (qs xs)"
  proof (induction xs rule: qs.induct)
    case 1 thus ?case by simp
  next
    case (2 p l)
    
    (* Introduce shortcut notation. Isabelle still sees expanded term, 
      it's just syntax sugar to make terms more concise to write! *)
    let ?l\<^sub>1 = "filter (\<lambda>x. x \<le> p) l"
    let ?l\<^sub>2 = "filter (\<lambda>x. x > p) l"
    
    (* Assume that recursive calls sort *)
    assume IH1: "sorted (qs ?l\<^sub>1)" and IH2: "sorted (qs ?l\<^sub>2)"
    
    (* Show that this call sorts *)
    show "sorted (qs (p#l))" proof -
      have "sorted (qs (p#l)) = sorted (qs ?l\<^sub>1 @ [p] @ qs ?l\<^sub>2)"
       (* Def. of qs *)
        by simp
      also have "\<dots> 
        = (sorted (qs ?l\<^sub>1) \<and> sorted (qs ?l\<^sub>2) 
          \<and> (\<forall>x\<in>set (qs ?l\<^sub>1). x\<le>p) \<and> (\<forall>x\<in>set (qs ?l\<^sub>2). p\<le>x))"
        (* sorted_lel *)
        by (simp add: sorted_lel[simplified])
      also have "\<dots>" proof (intro conjI)
        show "sorted (qs ?l\<^sub>1)" using IH1 .
        show "sorted (qs ?l\<^sub>2)" using IH2 .
        
        show "\<forall>x\<in>set (qs ?l\<^sub>1). x\<le>p" proof
          fix x 
          assume "x\<in>set (qs ?l\<^sub>1)" 
          hence "x\<in>set ?l\<^sub>1" by (simp add: qs_preserves_set)
          thus "x\<le>p" by (rule in_set_filter)
        qed  
       
        show "\<forall>x\<in>set (qs ?l\<^sub>2). x\<ge>p" 
          by (auto simp: qs_preserves_set) (* Analogously, thus written more concise here *)
          
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
    by auto

end
