module type S = sig

  type hdr
  type hdrVal
  type pol

  module HdrMap : Map.S with type key = hdr
  module HdrValSet : Set.S with type elt = hdrVal HdrMap.t

  type pred = hdrVal HdrMap.t
  type seq = hdrVal HdrMap.t
  type sum = HdrValSet.t
  type local =
    | Action of sum
    | ITE of pred * sum * local
  val compile : pol -> local
  val to_netkat : local -> pol  
end

module Make (Syntax : NetKAT_Syntax.S)  = struct
  type hdr = Syntax.hdr
  type hdrVal = Syntax.hdrVal
  type pol = Syntax.pol
  module HdrMap = Syntax.HdrMap
  module HdrValSet = Syntax.HdrValSet

  type pred = hdrVal HdrMap.t
  type seq = hdrVal HdrMap.t
  type sum = HdrValSet.t
  type local =
    | Action of sum
    | ITE of pred * sum * local

  open Syntax

  let id : seq = HdrMap.empty

  let drop : sum = HdrValSet.empty

  (* Only used by and_pred *)
  exception Empty_pred

  (* map_sum f (seq_1 + ... + seq_n) = f seq_1 + ... + f seq_n *)
  let map_sum (f : seq -> seq) (pol : sum) =
    let g seq pol' = HdrValSet.add (f seq) pol' in
    HdrValSet.fold g pol drop

  (* Some (pr1 ; pr2) unless the conjunct in empty, in which case, return None. *)
  let rec and_pred (pr1 : pred) (pr2 : pred) : pred option =
    let f hdr val1 val2 = match (val1, val2) with
      | (Some v1, Some v2) -> if v1 <> v2 then raise Empty_pred else Some v1
      | (Some v1, None) -> Some v1
      | (None, Some v2) -> Some v2
      | (None, None) -> failwith "and_pred impossible case" in
    try 
      Some (HdrMap.merge f pr1 pr2)
    with
      Empty_pred -> None

  (* s1 + s2 *)
  let rec par_sum_sum (s1 : sum) (s2 : sum) : sum = 
    HdrValSet.union s1 s2

  (* Lemma 1: if Y then S + S' else (S + A') = S + (if Y then S' else A')

       if Y then S + S' else (S + A')                      
     = Y;(S + S') + !Y;(S + A')                            if-then-else
     = Y;S + !Y;S + Y;S' + !Y;A'                           distributivity
     = (Y+!Y);S + (Y;S' + !Y;A')                           commutativity
     = 1;S + (Y;S' + !Y;A')                                excluded middle
     = S + (Y;S' + !Y;A')                                  *1
     = S + (if Y then S' else A')                          if-then-else

     QED
  *)

  (* simpl_par_sum_local S A = S + A *)
  let rec simpl_par_sum_local (s : sum) (l : local) : local = match l with
    (* Case A = S' is trivial *)
    | Action s' -> Action (par_sum_sum s s')
    (* Case A = if Y then S' else A'

         if Y then S + S' else [simpl_par_sum_local S A']    RHS below
       = if Y then S + S' else (S + A')                      induction
       = S + (if Y then S' else A')                          Lemma 1
       = S + A                                               substitution
    *)
    | ITE (y, s', a') -> ITE (y, par_sum_sum s s', simpl_par_sum_local s a')

  (* par_sum_local X S A B = if X then S + A else B *)
  let rec par_sum_local (x : pred) (s : sum) (a : local) (b : local) : local = 
    match a with
    (* Case A = S'

         if X then S + S' else B                                        RHS below
       = if X then S + A else B                                      substitution
    *)
    | Action s' -> ITE(x, par_sum_sum s s', b)
    (* Case A = if Y then S' else A'

         if X; Y then S + S' else [par_sum_local X S A' B]              RHS below
       = if X; Y then S + S' else if X then S + A' else B               induction
       = X;Y;(S + S') + !(X;Y);(if X then S + A' else B)             if-then-else
       = X;Y;(S + S') + (!X+!Y);(if X then S + A' else B)          de Morgans law
       = X;Y;(S + S') + !X;(if X then S + A' else B)               distributivity
                      + !Y;(if X then S + A' else B)         
       = X;Y;(S + S') + !X;B + !Y;(if X then S + A' else B)         contradiction
       = X;Y;(S + S') + !X;B + !Y;(X;(S+A') + !X;B)                  if-then-else
       = X;Y;(S + S') + !X;B + !Y;X;(S+A') + !Y;!X;B               distributivity
       = X;Y;(S + S') + !Y;X;(S+A') + (1+!Y);!X;B                  distributivity
       = X;Y;(S + S') + !Y;X;(S+A') + !X;B                                    b+1             
       = if X then Y;(S + S') + !Y;(S + A') else B                   if-then-else
       = if X then (if Y then S + S' else S + A') else B             if-then-else
       = if X then (S + if Y then S' else A') else B                      Lemma 1
       = if X then (S + A) else B                                    substitution
    *)
    | ITE (y, s', a') -> 
      let else_branch = par_sum_local x s a' b in
      match and_pred x y with
      | None -> else_branch
      | Some x_and_y ->
        ITE (x_and_y, par_sum_sum s s', else_branch)

  (* par_local_local A B = A + B *)
  let rec par_local_local (a : local) (b : local) : local = match (a, b) with
    (* Immediate *)
    | (_ , Action s) -> simpl_par_sum_local s a
    (* Commutativity, then immediate *)
    | (Action s, _) -> simpl_par_sum_local s b
    (* Case A = if X then A' else B'

         par_sum_local X A' B (par_local_local B' B)                    RHS below
       = par_sum_local X A' B (B' + B)                                  induction
       = if X then A' + B else B' + B                               par_sum_local
       = (if X then A' else B') + B                                       Lemma 1
       = A + B                                                       substitution
    *)
    | (ITE (x, a', b'), _) ->  par_sum_local x a' b (par_local_local b' b)

  (* seq_seq H V SEQ = H<-V; SEQ *)
  let seq_seq (h : hdr) (v : hdrVal) (seq : seq) : seq = 
    (* If SEQ already sets H to anything, then that setting overrides *)
    if HdrMap.mem h seq then seq
    (* Otherwise, return a SEQ with H <- V *)
    else HdrMap.add h v seq

  (* commute_sum H V S = H <- V; S *)
  let commute_sum (h : hdr) (v : hdrVal) (s : sum) : sum =
    map_sum (seq_seq h v) s (* distributivity *)

  (* pr is a conjunct, so if h is not bound, then it is matches h = v

    pred_matches h v pr = false => pr; h=v = 0 
    pred_matches h v pr = false => h=v; pr = 0 
   *)
  let rec pred_matches (h : hdr) (v : hdrVal) (pr : pred) : bool =
    not (HdrMap.mem h pr) || HdrMap.find h pr = v

  let rec pred_wildcard (h : hdr) (pr : pred) : pred =
    HdrMap.remove h pr

  (* commute H V P = H<-V; P *)
  let rec commute (h : hdr) (v : hdrVal) (p : local) : local = match p with
    (* = commute_sum h v sum                                             RHS below
       = h <- v; sum                                                   commute_sum
     *)
    | Action sum -> Action (commute_sum h v sum)
    (*  = commute h v (if pr then sum else pol)                          LHS below
     *)
    | ITE (pr, sum, pol) ->
      match pred_matches h v pr with
      (* = commute h v pol                                               RHS below
         = h<-v; pol                                                     induction
         = h<-v; if false then sum else pol                       definition of if
         = h<-v; if h=v; pr then sum else pol          pred_matches h v pr = false
         = h<-v; (h=v; pr; sum + !(h=v; pr); pol)                 definition of if
         = h<-v; (h=v; pr; sum + (h!=v + !pr); pol)                de Morgan's law
         = h<-v; (h=v; pr; sum + h!=v; pol + !pr; pol)              distributivity
         = h<-v; h=v; pr; sum + h<-v; h!=v; pol + h<-v; !pr; pol    distributivity
         = h<-v; pr; sum + 0 + h<-v; !pr; pol                       h<-v; h!=v = 0
         = h<-v; (pr; sum + !pr; pol)                               distributivity
         = h<-v; (if pr them sum else pol)                                    goal

       *) 
      | false -> commute h v pol
      (* = if pred_wildcard h pr then commute_sum h v sum                RHS below
           else commute h v pol
         = if pred_wildcard h pr then (h<-v; sum) else (h<-v;pol)        induction
         = h<-v; if pred_wildcard h pr then sum elese pol           distributivity
         = CONTINUE
        *)
      | true -> ITE (pred_wildcard h pr, commute_sum h v sum, commute h v pol)

  (* norm_ite pr pol1 pol2 = if pr then pol1 else pol2
   *)
  let rec norm_ite (pr : pred) (pol1 : local) (pol2 : local) : local =
    match pol1 with
    (* Case 
         norm_ite pr sum1 pol2
       = if pr then sum1 else pol2
     *)
    | Action sum1 -> ITE (pr, sum1, pol2)
    (* Case 
         norm_ite pr (if pr1' then sum1' else pol1')  pol2                    case
       = if pr && pr1' then sum1' else norm_ite pr pol1' pol2        by definition
       = if pr && pr1' then sum1' else (if pr then pol1' else pol2)   by induction
       = (pr && pr1'); sum1' + !(pr && pr1'); (if pr then pol1' else pol2)
       = (pr && pr1'); sum1' + !(pr && pr1'); (pr; pol1' + !pr; pol2)
       = pr; pr1'; sum1' + (!pr + !pr1'); (pr; pol1' + !pr; pol2)
       = pr; pr1'; sum1' + !pr;   (pr; pol1' + !pr; pol2) + 
                           !pr1'; (pr; pol1' + !pr; pol2)
       = pr; pr1'; sum1' + !pr; pol2 + !pr1'; pr; pol1' + !pr1'; !pr; pol2
       = pr; (pr1'; sum1' + !pr1'; pol1') + !pr; (pol2 + !pr1'; pol2)
       = pr; (pr1'; sum1' + !pr1'; pol1') + !pr; pol2
       = if pr then (if pr1' then sum1' else pol1') else pol2                 goal
     *)
    | ITE (pr1', sum1', pol1') ->
      match and_pred pr pr1' with
      | None -> norm_ite pr pol1' pol2
      | Some pr1_and_pr1' -> ITE (pr1_and_pr1', sum1', norm_ite pr pol1' pol2)

  (* seq_seq_local p1 p2 = p1; p2

      fold commute {p11, ..., p1n} p2
    
     Case n = 0

       fold commute {} p2 = p2

     Case n > k

       fold commute (h1<-v1; ... ;hn<-vn) p2
     = commute h1 v1 (commute h2 v2 ( ... commute hn vn p2 ) )
     = h1<-v2; h2<-v2; ...; hn<-vn; p2
   *)
  let seq_seq_local (p1 : seq) (p2 : local) : local = 
    HdrMap.fold commute  p1 p2

  (* seq_sum_local p1 p2 = p1; p2

       HdrValSet.fold (fun seq acc -> 
         par_local_local (seq_seq_local seq p2) acc)
         p1 drop

     HdrValSet.fold (fun x v -> f x v) init lst

    if P(init) and P(V) => P(f x v) then 

      P 
  *)
  let seq_sum_local (p1 : sum) (p2 : local) : local = 
    let lst = HdrValSet.fold (fun elt lst -> elt :: lst) p1 [] in
    let rec loop lst = match lst with
      | [] -> Action drop
      | seq :: lst' ->
        par_local_local (seq_seq_local seq p2) (loop lst') in
    loop lst

  (* seq_local_local pol1 pol2 = pol1; pol2 *)
  let rec seq_local_local (pol1 : local) (pol2 : local) : local = match pol1 with
    (* = seq_sum_local sum1 pol2                                         RHS below
       = sum1; pol2                                        proof for seq_sum_local
       = pol1; pol2                                                  by definition
     *)
    | Action sum1 -> seq_sum_local sum1 pol2
    (* = seq_local_local (if pred1 then sum1 else pol1') pol2           case below
       = norm_ite pred1 (seq_sum_local sum1 pol2)                        RHS below
                        (seq_local_local pol1' pol2)
       = norm_ite pred1 (seq_sum_local sum1 pol2) (pol1'; pol2)       by induction
       = norm_ite pred1 (sum1; pol2) (pol1'; pol2)                   seq_sum_local
       = if pred1 then (sum1; pol2) else pol1'; pol2)                     norm_ite
       = (if pred1 then sum1 else pol1'); pol2                      distributivity
       = pol1; pol2                                                  by definition
     *)
    | ITE (pred1, sum1, pol1') ->
      norm_ite pred1 (seq_sum_local sum1 pol2) (seq_local_local pol1' pol2)

  let is_drop (pol : sum) : bool =
    HdrValSet.is_empty pol

  (* there is only one element, and it is the empty sequence of updates *)
  let is_id (pol : sum) : bool =
    not (HdrValSet.is_empty pol) && HdrMap.is_empty (HdrValSet.choose pol)

  (*
      !(if A then X else IND)
    = !(A; X + !A; IND)           by definition of if .. then .. else
    = !(A; X) ; !(!A; IND)        de Morgan's law

    Case X = 1:

        !(A; X) ; !(!A; IND)       from above
      = !(A; 1) ; !(!A; IND)       substitute X = 1
      = !A; !(!A; IND)             identity
      = !A; (!!A + !IND)           de Morgan's law
      = !A; (A + !IND)             double negation
      = !A; A + !A; !IND           distributivity
      = 0 + !A; !IND               excluded middle
      = if A then 0 else 1; !IND   by defn. of if-then-else

      !IND can be normalized by induction and the product can be normalized
      by the seq_local_local function.

    Case X = 0:

        !(A; X) ; !(!A; IND)       from above
      = !(A; 0) ; !(!A; IND)       substitute X = 0
      = !0      ; !(!A; IND)       zero
      = 1; !(!A; IND)              negation
      = !(!A; IND)                 identity
      = !!A + !IND                 de Morgan's law
      = A + !IND                   double negation
      = if A then 1 else 0 + !IND  by defn. of if-then-else

      !IND can be normalized by induction and the sum can be normalized
      by the par_local_local function.
  *)
  let rec negate (pred : local) : local = match pred with
    | Action sum ->
      if is_drop sum then
        Action (HdrValSet.singleton id)
      else if is_id sum then
        Action drop
      else
        failwith "not a predicate"
    | ITE (a, x, ind) ->
      if is_drop x then
        par_local_local 
          (ITE (a, HdrValSet.singleton id, Action drop))
          (negate ind)
      else if is_id x then
        seq_local_local
          (ITE (a, drop, Action (HdrValSet.singleton id)))
          (negate ind)
      else
        failwith "not a predicate"

  and local_normalize (pol : pol) : local = match pol with
    | Drop ->
      Action drop (* missing from appendix *)
    | Id ->
      Action (HdrValSet.singleton HdrMap.empty) (* missing from appendix *)
    | Neg p ->
      negate (local_normalize p)
    | Test (h, v) ->
      ITE (HdrMap.singleton h v, HdrValSet.singleton id, Action drop)
    | Set (h, v) ->
      Action (HdrValSet.singleton (HdrMap.singleton h v))
    | Par (pol1, pol2) ->
      (* In Lemma 30, cases 2--4 p,q should be written using if..then..else
         shorthand. *)
      par_local_local (local_normalize pol1) (local_normalize pol2)
    | Seq (pol1, pol2) ->
      seq_local_local (local_normalize pol1) (local_normalize pol2)


  let pred_to_netkat pr =
    (* avoid printing trailing Id if it is unnecessary *)
    if HdrMap.is_empty pr then
      Id
    else
      let (h, v) = HdrMap.min_binding pr in
      let pr' = HdrMap.remove h pr in
      let f h v pol = Seq (Test (h, v), pol) in
      HdrMap.fold f pr' (Test (h, v))

  let seq_to_netkat (pol : seq) : pol =
    (* avoid printing trailing Id if it is unnecessary *)
    if HdrMap.is_empty pol then
      Id
    else
      let (h, v) = HdrMap.min_binding pol in
      let pol' = HdrMap.remove h pol in
      let f h v pol' = Seq (Set (h, v), pol') in
      HdrMap.fold f pol' (Set (h, v))

  let sum_to_netkat (pol : sum) : pol = 
    (* avoid printing trailing Drop if it is unnecessary *)
    if HdrValSet.is_empty pol then
      Drop
    else
      let f seq pol' = Par (seq_to_netkat seq, pol') in
      let seq = HdrValSet.min_elt pol in
      let pol' = HdrValSet.remove seq pol in
      HdrValSet.fold f pol' (seq_to_netkat seq)

  let rec to_netkat (pol : local) : pol = match pol with
    | Action sum -> sum_to_netkat sum
    | ITE (pred, sum, pol') ->
      let pr = pred_to_netkat pred in
      Par (Seq (pr, sum_to_netkat sum),
             Seq (Neg pr, to_netkat pol'))

  let compile = local_normalize
end