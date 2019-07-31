(*<*)
theory Talk
  imports Demo
begin

setup \<open>
  let



    fun report_text ctxt text =
      Context_Position.report ctxt (Input.pos_of text)
        (Markup.language_text (Input.is_delimited text));
  
    fun trim_blank_lines txt = let
      fun tr (lines as l1::l2::ls) = if forall Symbol.is_blank (Symbol.explode l1) then l2::ls else lines
        | tr lines = lines

      fun tr_line l = if forall Symbol.is_blank (Symbol.explode l) then "" else l

      fun is_empty l = l=""

    in
      txt 
      |> split_lines 
      |> map tr_line
      |> drop_prefix is_empty
      |> drop_suffix is_empty
      |> space_implode "\n"
    end

    local
      fun min_ls [] = 0
        | min_ls ([]::xs) = min_ls xs
        | min_ls (x::xs) = let 
            val n = min_ls xs 
            val m = find_index (not o Symbol.is_space) x
          in if n=0 orelse m<n then m else n end
  
      fun indent_line isub iadd = drop isub #> append (replicate iadd Symbol.space)
    in
      fun auto_indent ctxt txt = let
        val lines = split_lines txt |> map Symbol.explode
        val isub = min_ls lines
        val iadd = Config.get ctxt Document_Antiquotation.thy_output_indent
        val lines = map (indent_line isub iadd) lines
      in
        lines |> map implode |> space_implode "\n"
      end
    end

    
    fun enclose txt = "\<^starttext>" ^ txt ^ "\<^endtext>"
    
    fun prepare_lines ctxt txt = 
      enclose (
        if Config.get ctxt Document_Antiquotation.thy_output_display then 
             txt 
          |> trim_blank_lines 
          |> auto_indent ctxt
        else
          txt |> split_lines |> map Symbol.trim_blanks |> space_implode " "
      )

    fun prepare_text ctxt =
      Input.source_content #> fst #> prepare_lines ctxt;

    fun theory_text_antiquotation name =
      Thy_Output.antiquotation_raw name (Scan.lift Args.text_input)
        (fn ctxt => fn text =>
          let
            val keywords = Thy_Header.get_keywords' ctxt;
    
            val _ = report_text ctxt text;
            val _ =
              Input.source_explode text
              |> Token.tokenize keywords {strict = true}
              |> maps (Token.reports keywords)
              |> Context_Position.reports_text ctxt;
          in
            prepare_text ctxt text
            |> Token.explode0 keywords
            |> maps (Thy_Output.output_token ctxt)
            |> Thy_Output.isabelle ctxt
          end);

    fun text_antiquotation name = 
      Thy_Output.antiquotation_raw name (Scan.lift Args.text_input)
      (fn ctxt => fn text =>
        let
          val _ = report_text ctxt text;
        in
          prepare_text ctxt text
          |> Thy_Output.output_source ctxt
          |> Thy_Output.isabelle ctxt
        end)

  in
       text_antiquotation \<^binding>\<open>text\<close>
    #> text_antiquotation \<^binding>\<open>cartouche\<close>
    #> theory_text_antiquotation \<^binding>\<open>theory_text\<close>

  end
\<close>

declare [[show_question_marks = false, eta_contract = false]]

(*>*)

section \<open>Introduction\<close>

text \<open>\color{black}
  \begin{frame}{Introduction}
    Programming and proving correct quicksort
    \pause\medskip
    
    using the Theorem Prover Isabelle/HOL
    \<^url>\<open>https://isabelle.in.tum.de/\<close>
    \pause\medskip
    
    download it and follow this lecture on your laptop!\\
    Lecture Material: \<^url>\<open>https://github.com/lammich/MCR_SS_2019_FunProgProve\<close>
    \pause\medskip

    Relax and enjoy! There is no exam on this lecture!
  \end{frame}


  
  \begin{frame}{Short Poll}
    Raise your hand if you
    \<^item><+-> Have ever written a computer program
      \<^item><+-> in C, C++, Java, BASIC, PASCAL
      \<^item><+-> in JavaScript
      \<^item><+-> in PHP, Python, Ruby, PERL
      \<^item><+-> in Haskell, Scala, OCaml, SML, LISP, Scheme
    \<^item><+-> Know what quicksort is  
    \<^item><+-> Know what (structural) induction means
    \<^item><+-> Have ever used an interactive theorem prover
    
  \end{frame}

  \begin{frame}{Lists}
    \<^descr>[\<^term>\<open>[]\<close>] Empty list
    \<^descr>[\<^term>\<open>a#l\<close>] List with first element \<^term>\<open>a\<close> and then list \<^term>\<open>l\<close>
    \pause\medskip
    
    Example: \<open>1#2#3#4#[]\<close>
    \pause\medskip
    
    Notation: \<^term>\<open>[1::nat,2,3,4]\<close>
    \pause\medskip
    
    \<^term>\<open>l\<^sub>1@l\<^sub>2\<close>: concatenate two lists
    
    Example: \<^term>\<open>[1::nat,2,3]@[4,5,6] = [1,2,3,4,5,6]\<close>
    
  \end{frame}

  \begin{frame}{Append \<open>@\<close>}
    How to define \<open>@\<close>? \pause Using only \<open>[]\<close> and \<open>#\<close>?
    \pause\medskip
    
    Case distinction whether first list is empty:
        
    \<^term>\<open>[]@l\<^sub>2\<close> = \pause \<^term>\<open>l\<^sub>2\<close> \pause \\
    \<^term>\<open>(x#l\<^sub>1)@l\<^sub>2\<close> = \pause \<open>x # (l\<^sub>1 @ l\<^sub>2)\<close>
    \pause\medskip 
    
    Example: \\
      \<open>([1,2] @ [3])\<close>          
      \pause= \<open>(1 # 2 # []) @ (3 # [])\<close>\\
      \pause= \<open>1 # (( 2 # []) @ (3 # []))\<close>\\
      \pause= \<open>1 # 2 # ([] @ (3 # []))\<close>\\
      \pause= \<open>1 # 2 # 3 # []\<close>
  
  \end{frame}  
                               
  \begin{frame}{Filter}
    Erase all elements \high{not} \<open>\<le> 4\<close> from a list
    \pause\medskip
    
    \<open>leq4 [1,42,7,5,2,6,3]\<close> \pause= \<open>[1,2,3]\<close>
    
    \pause\medskip
    
    \<open>leq4 []\<close> = \pause \<open>[]\<close> \pause\\
    \<open>leq4 (x#l)\<close> = \pause \<open>if x\<le>4 then x # leq4 l else leq4 l\<close>
    
    \pause\medskip
    
    \<^term>\<open>leq4 [1,42,7,5,2,6,3]\<close>\\
    \pause= \<^term>\<open>1 # leq4 [42,7,5,2,6,3]\<close>\\
    \pause= \<^term>\<open>1 # leq4 [7,5,2,6,3]\<close>\\
    \pause= \<^term>\<open>1 # leq4 [5,2,6,3]\<close>\\
    \pause= \<^term>\<open>1 # leq4 [2,6,3]\<close>\\
    \pause= \<^term>\<open>1 # 2 # leq4 [6,3]\<close>\\
    \pause= \<^term>\<open>1 # 2 # leq4 [3]\<close>\\
    \pause= \<^term>\<open>1 # 2 # 3 # leq4 []\<close>\\
    \pause= \<open>1 # 2 # 3 # []\<close>
    
  \end{frame}
  
  \begin{frame}{Filter}
    Condition as parameter to function
    @{thm[display] filter.simps(1) filter.simps(2)[where xs=l]}
    \pause\medskip

    \<^term>\<open>filter (\<lambda>x. x\<le>4) l\<close>: Same as \<open>leq4\<close>
    \pause\medskip
    
    \<^term>\<open>(\<lambda>x. x\<le>4)\<close> is anonymous function, with parameter \<open>x\<close>.
  
  \end{frame}
  
  \thyfile{Demo}{Functions}
  
  \begin{frame}{Count}
    \<^term>\<open>count l x\<close> How often does element \<open>x\<close> occur in list \<open>l\<close>
    \pause\medskip

    Example: \<^term>\<open>count [1,2,3,1,2,3,2,2] 2\<close> = \pause \<open>4\<close>
    \pause\medskip

    \<^term>\<open>count [] x\<close> = \pause \<open>0\<close> \pause\\
    \<^term>\<open>count (y#l) x\<close> = \pause \<open>if x=y then 1 + count l x else count l x\<close>
    \pause\medskip

    \<^term>\<open>count [2,2,1,2] 2\<close> \\
    = \pause \<^term>\<open>1 + count [2,1,2] 2\<close> \\
    = \pause \<^term>\<open>1 + 1 + count [1,2] 2\<close> \\
    = \pause \<^term>\<open>1 + 1 + count [2] 2\<close> \\
    = \pause \<^term>\<open>1 + 1 + 1 + count [] 2\<close> \\
    = \pause \<^term>\<open>1 + 1 + 1 + (0::nat)\<close> \\
    = \pause \<^term>\<open>3::nat\<close> \\
  
  \end{frame}
  
  \begin{frame}{Sortedness}
    Is a list sorted? E.g. \<^term>\<open>sorted [1,2,4::nat] = True\<close>, \<^term>\<open>sorted [1,4::nat,3] = False\<close>
    \pause\medskip

    \<^term>\<open>sorted []\<close> = \pause \<^term>\<open>True\<close> \pause\\
    \<^term>\<open>sorted [x]\<close> = \pause \<^term>\<open>True\<close> \pause\\
    \<^term>\<open>sorted (x#y#l)\<close> = \pause \<^term>\<open>x\<le>y \<and> sorted (y#l)\<close>
    \pause\medskip
    
    Note \<open>\<and>\<close> means "and".
  \end{frame}

  \thyfile{Demo}{Count and Sortedness}
  
  \begin{frame}{Quicksort}
    Algorithm to sort a list
    \pause\medskip
    
    Idea: 
      \<^enum> pick pivot element \<open>p\<close> (e.g. first element of list)
      \<^enum> partition list into elements \<open>\<le> p\<close> and \<open>> p\<close>
      \<^enum> recursively sort partitions
    
    \pause\medskip
    \<^term>\<open>qs [3,2,5,4,7]\<close> \\
    = \pause \<^term>\<open>qs [2] @ [3] @ qs [5,4,7]\<close> \\
    = \pause \<^term>\<open>[2] @ [3] @ (qs [4] @ [5] @ qs [7])\<close> \\
    = \pause \<^term>\<open>[2::nat] @ [3] @ ([4] @ [5] @ [7])\<close> \\
    = \pause \<^term>\<open>[2::nat,3,4,5,7]\<close>
    \pause\medskip
    
    \<^term>\<open>qs [] = []\<close> \\
    @{term [source] \<open>qs (p # l) = qs (filter (\<lambda>x. x \<le> p) l) @ [p] @ qs (filter (\<lambda>x. x > p) l)\<close>}
  \end{frame}

  \thyfile{Demo}{Quicksort}
  
  
  \begin{frame}{Correct Sorting}
    What does it mean that quicksort is \high{correct}?
    \pause\medskip

    \<^enum><+-> The resulting list must be sorted \<^prop>\<open>sorted (qs l)\<close>
    \<^enum><+-> and must contain same elements \<^prop>\<open>\<forall>x. count (qs l) x = count l x\<close>
    \medskip

    \<open>\<forall>x. \<dots>\<close> means "for all \<open>x\<close>"
  
  \end{frame}
    
  \thyfile{Demo}{Correctness of Sorting}
    
  \begin{frame}{Useful Properties}
    \<^term>\<open>count (l\<^sub>1@l\<^sub>2) x\<close> = \pause \<^term>\<open>count l\<^sub>1 x + count l\<^sub>2 x\<close>
    \pause\medskip
    
    \<^term>\<open>count (filter P l) x\<close> = \pause \<^term>\<open>(if P x then count l x else 0)\<close>
    \pause\medskip
    
    @{term [source] 
      \<open>count (filter (\<lambda>x. x \<le> p) l) x + count (filter (\<lambda>x. x > p) l) x\<close>} = \pause \<^term>\<open>count l x\<close>
  
  \end{frame}
  
  
  
\<close>



(*<*)
end
(*>*)
