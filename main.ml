(* Question1 *)

type transition = int * char * int
type aef = {
  alphabet:char list ; (* {a,b}*)
  initial_etat : int; (* 1 * état source *) 
  etats : int list ;  (* {1, 2, 3}*)
  lamda : transition list; (*lamda*)
  accepte_etat : int list (*{3}*)
}
(*Question 2: vérifie s'il existe une transition pour chaque caratère*)
  let rec exist_dans_la_liste = fun number q -> 
    match q with 
    |[] -> false 
    |h::t -> if number = h then true 
    else exist_dans_la_liste number t;;

let rec sous_ensemble = fun f q  -> 
  match f with 
  |[] -> true 
  |h::t -> if exist_dans_la_liste h q then sous_ensemble t q 
  else false
;;
(* vérifie source et cible dans transition 
   List.exist vérifie si au moin un élément de la liste satisfait au prédicat*)
let rec est_source_ou_cible = fun etat transition ->
  List.exists(fun(src,_,cib) -> src = etat || cib = etat) transition
;;

let est_correct = fun aef -> 
  let non_vide = aef.etats != [] in 
  let final_sous_ensemble = sous_ensemble aef.accepte_etat aef.etats in 
  let non_utilise = List.for_all(fun s -> est_source_ou_cible s aef.lamda) aef.etats in 
  non_vide && final_sous_ensemble && non_utilise 
;;

(* Question 3  *)

let est_complet a =
  let transitions_pour_etat etat =
    List.filter (fun (src, _, _) -> src = etat) a.lamda
  in
  let transitions_complete etat =
    List.length (transitions_pour_etat etat) = List.length a.alphabet
  in
  List.for_all transitions_complete a.etats
let completer a =
  if est_complet a then a
  else
    let etat_puits = List.fold_left max 0 a.etats + 1 in
    let transitions_manquantes =
      List.fold_left
        (fun acc etat ->
          List.fold_left
            (fun acc2 sym ->
              match
                List.find_opt
                  (fun (src, c, _) -> src = etat && c = sym)
                  a.lamda
              with
              | Some _ -> acc2
              | None -> (etat, sym, etat_puits) :: acc2)
            acc a.alphabet)
        [] a.etats
    in
    {
      a with
      etats = etat_puits :: a.etats;
      lamda = a.lamda @ transitions_manquantes;
    }

  ;;
  (* Questin 4  *)
  (* Fonctions pour compléter un AEF *)
let transitions_complete etat alphabet transitions =
  List.for_all (fun x -> List.exists (fun (src, c, _) -> src = etat && c = x) transitions) alphabet
;;
let transitions_manquantes_etat etat alphabet transitions =
  List.fold_left (fun acc x -> if not (List.exists (fun (src, c, _) -> src = etat && c = x) transitions) then x :: acc else acc) [] alphabet
;;
let transitions_manquantes a =
  List.fold_left (fun acc etat -> if not (transitions_complete etat a.alphabet a.lamda) then (etat, transitions_manquantes_etat etat a.alphabet a.lamda) :: acc else acc) [] a.etats
;;
let completer a =
  if a.lamda = [] || a.accepte_etat = [] then a
  else
    let etat_puits = List.fold_left max 0 a.etats + 1 in
    let nouvelles_transitions = List.fold_left (fun acc (etat, manquantes) -> List.fold_left (fun acc2 x -> (etat, x, etat_puits) :: acc2) acc manquantes) a.lamda (transitions_manquantes a) in
    { a with etats = etat_puits :: a.etats; lamda = nouvelles_transitions }
  ;;

(* Question 5  *)
(* Fonction pour vérifier si un AEF reconnaît le langage vide *)
let langage_vide a =
  let rec atteindre_etat_acceptant etat visited =
    if List.mem etat visited then false
    else if List.mem etat a.accepte_etat then true
    else
      let next_etats = List.fold_left (fun acc (src, _, tgt) -> if src = etat then tgt :: acc else acc) [] a.lamda in
      List.exists (fun etat -> atteindre_etat_acceptant etat (etat :: visited)) next_etats
  in
  not (atteindre_etat_acceptant a.initial_etat [])
;;
(* Question 6 *)
(* Fonction pour vérifier si un AEF est déterministe *)
let est_deterministe a =
  let rec transition_unique etat x transitions =
    match transitions with
    | [] -> true
    | (src, c, _) :: t ->
      if src = etat && c = x then
        List.for_all (fun (src', c', _) -> not (src' = etat && c' = x)) t
      else transition_unique etat x t
  in
  List.for_all (fun etat -> List.for_all (fun x -> transition_unique etat x a.lamda) a.alphabet) a.etats
;;
(* Question 7  *)

type etat_option = None | Some of int
let lecture_car (etat: int) (car: char) (delta: transition list): etat_option =
  let transition_opt = List.find_opt (fun (src, c, _) -> src = etat && c = car) delta in
  match transition_opt with
  | None -> None
  | Some (_, _, tgt) -> Some tgt
;;

(* Question 8  *)
let rec lecture_mot (etat: int) (mot: string) (delta: transition list): etat_option =
  if String.length mot = 0 then
    Some etat
  else
    let car = mot.[0] in
    let reste_mot = String.sub mot 1 (String.length mot - 1) in
    match lecture_car etat car delta with
    | None -> None
    | Some next_etat -> lecture_mot next_etat reste_mot delta
  ;;

  (* Question 9  *)
  let accepter_mot (mot: string) (a: aef): bool =
    match lecture_mot a.initial_etat mot a.lamda with
    | None -> false
    | Some final_etat -> List.mem final_etat a.accepte_etat

  
    (* Quesion 10 *)
    let union_aefs (a1: aef) (a2: aef): aef =
      let q0 = (List.fold_left max 0 (a1.etats @ a2.etats)) + 1 in
      let etats = q0 :: (a1.etats @ a2.etats) in
      let alphabet = List.sort_uniq compare (a1.alphabet @ a2.alphabet) in
      let initial_etat = q0 in
      let accepte_etat = if List.mem a1.initial_etat a1.accepte_etat || List.mem a2.initial_etat a2.accepte_etat
                         then q0 :: (a1.accepte_etat @ a2.accepte_etat)
                         else a1.accepte_etat @ a2.accepte_etat in
      let transitions_q0 = List.concat
        [ List.map (fun (src, x, tgt) -> (q0, x, tgt)) (List.filter (fun (src, _, _) -> src = a1.initial_etat) a1.lamda)
        ; List.map (fun (src, x, tgt) -> (q0, x, tgt)) (List.filter (fun (src, _, _) -> src = a2.initial_etat) a2.lamda) ] in
      let lamda = transitions_q0 @ a1.lamda @ a2.lamda in
      { alphabet; initial_etat; etats; lamda; accepte_etat };;

      (* Question 11 *)
      let concatenation_aefs (a1: aef) (a2: aef): aef =
        let etats = a1.etats @ a2.etats in
        let alphabet = List.sort_uniq compare (a1.alphabet @ a2.alphabet) in
        let initial_etat = a1.initial_etat in
        let accepte_etat = if List.mem a2.initial_etat a2.accepte_etat
                           then a1.accepte_etat @ a2.accepte_etat
                           else a2.accepte_etat in
        let transitions_connectees = List.concat
          [ List.concat (List.map (fun src ->
            List.map (fun (s, x, tgt) -> (src, x, tgt)) (List.filter (fun (src, _, _) -> src = a2.initial_etat) a2.lamda))
            (List.filter (fun s -> List.mem s a1.accepte_etat) a1.etats)) ] in
        let lamda = transitions_connectees @ a1.lamda @ a2.lamda in
        { alphabet; initial_etat; etats; lamda; accepte_etat }
      ;;

        let afficher (a: aef): unit =
          let afficher_transition (src, x, tgt) =
            Printf.printf "%d -> (%c) %d\n" src x tgt
          in
          List.iter afficher_transition a.lamda;;

          let itere (a: aef): aef =
            let q0 = List.fold_left max 0 a.etats + 1 in
            let transitions_q0 = List.filter (fun (src, _, _) -> src = a.initial_etat) a.lamda in
            let transitions_q0' = List.map (fun (src, x, tgt) -> (q0, x, tgt)) transitions_q0 in
            let transitions_f1 = List.flatten (List.map (fun f -> List.filter (fun (_, _, tgt) -> tgt = f) a.lamda) a.accepte_etat) in
            let transitions_f1' = List.map (fun (src, x, tgt) -> (src, x, q0)) transitions_f1 in
            let nouvelles_transitions = a.lamda @ transitions_q0' @ transitions_f1' in
            let nouveaux_etats_acceptants = q0 :: a.accepte_etat in
            { a with etats = q0 :: a.etats; initial_etat = q0; lamda = nouvelles_transitions; accepte_etat = nouveaux_etats_acceptants }
