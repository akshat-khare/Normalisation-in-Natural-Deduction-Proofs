open List;;
type prop = T| F | L of string
			| Not of prop
			| And of prop * prop
			| Or of prop * prop
			| Impl of prop * prop
		;;
let rec isSameProp a b = match (a,b) with
| (T,T) -> true
| (F,F) -> true
| (L(c), L(d)) -> if(c=d) then true else false
| (Not(c), Not(d)) -> (isSameProp c d)
| (And(c, d), And(e, f)) -> (isSameProp c e) && (isSameProp d f)
| (Or(c, d), Or(e, f)) -> (isSameProp c e) && (isSameProp d f)
| (Impl(c, d), Impl(e, f)) -> (isSameProp c e) && (isSameProp d f)
| _ -> false
;;
let rec isMember a l = match l with
| [] -> false
| x::xs -> if((isSameProp x a)) then true else (isMember a xs)
;;
let rec isContained l1 l2 = match l1 with
| [] -> true
| x::xs -> if(isMember x l2) then (isContained xs l2) else false
;;
let isSameList l1 l2 = (isContained l1 l2) && (isContained l2 l1)
;;
type gamma = prop list;;
type rule = Hyp | Itrue | Iimplies | Eimplies | Eint | Classical | Iand | Eleftand | Erightand | Ileftor | Irightor | Eor;;
type ndprooftree = Rule of gamma * prop* rule * ndprooftree list;;
let extractgamma proof = match proof with
| Rule (gamma, prop, rule, childproof) -> gamma;;
let extractprop proof = match proof with
| Rule (gamma, prop, rule, childproof) -> prop;;
let extractchildproof proof = match proof with
| Rule (gamma, prop, rule, childproof) -> childproof;;
let extractrule proof = match proof with
| Rule (gamma, prop, rule, childproof) -> rule;;
let rec mergeList g delta = match delta with
| [] -> g
| x::xs -> if(isMember x g) then (mergeList g xs) else (mergeList (g@[x]) xs)
;;

let rec pad delta proof = match proof with
| Rule (gamma, prop, rule, childproof) -> Rule((mergeList gamma delta), prop, rule, (map (pad delta) childproof))
;;

exception InvalidProof;;
let rec setGamma minGaama proof = match proof with
| Rule (gamma, prop, rule, childproof) -> (match rule with
											| Iimplies -> (match prop with
															| Impl(p,q) -> (Rule (minGaama, prop, rule, (map (setGamma (p::minGaama)) childproof)))
															| _ -> (raise InvalidProof)
															)
											| Classical -> (Rule(minGaama, prop, rule, (map (setGamma ((Not prop)::minGaama)) childproof)))
											| _ -> (Rule(minGaama, prop, rule, (map (setGamma minGaama) childproof)))
										)
;;
exception InvalidGaama;;
let rec subtractgaama gaamabig gaamasmall = match gaamabig with
| [] -> raise InvalidGaama
| x::xs -> if(isMember x gaamasmall) then (subtractgaama xs gaamasmall) else x
;;
exception Normalised;;

let isrpair proof = match proof with
| Rule (gamma, prop, rule, childproof) -> (match rule with
											| Eimplies -> (
															let checkproof = hd childproof in
															let checkrule = extractrule checkproof in
															(match checkrule with
															| Iimplies -> (
																			let proxySameprop = extractprop (hd (extractchildproof checkproof)) in
																			(isSameProp prop proxySameprop)
																			)
															| _ -> false)
														)
											| Eleftand -> (
															let checkproof = hd childproof in
															let checkrule = extractrule checkproof in
															(match checkrule with
															| Iand -> (
																			let proxySameprop = extractprop (hd (extractchildproof checkproof)) in
																			(isSameProp prop proxySameprop)
																			)
															| _ -> false)
														)
											| Erightand -> (
															let checkproof = hd childproof in
															let checkrule = extractrule checkproof in
															(match checkrule with
															| Iand -> (
																			let proxySameprop = extractprop (hd (tl (extractchildproof checkproof))) in
																			(isSameProp prop proxySameprop)
																			)
															| _ -> false)
														)
											| Eor -> (
															let checkproof = hd childproof in
															let checkrule = extractrule checkproof in
															let propp = subtractgaama (extractgamma (hd (tl childproof))) gamma in
															let propq = subtractgaama (extractgamma (hd (tl (tl childproof)))) gamma in
															(match checkrule with
															| Ileftor -> (
																			let proxySameprop = extractprop (hd (extractchildproof checkproof)) in
																			(isSameProp propp proxySameprop)
																			)
															| Irightor -> (
																			let proxySameprop = extractprop (hd (extractchildproof checkproof)) in
																			(isSameProp propq proxySameprop)
																			)
															| _ -> false)
														)
											| _ -> false)
;;

let rec find_rpair_with_path proof path = match proof with
| Rule (gamma, prop, rule, childproof) -> (match rule with
											| Eimplies -> (
															let checkproof = hd childproof in
															let checkprop = extractprop checkproof in
															(match childprop with
															| Iimplies -> (
																			let proxySameprop = extractprop (hd (extractchildproof checkproof)) in
																			if(isSameProp prop proxySameprop)
																				then (proof,path)
																			else 
																				()
																			)
															| _ -> expr2)
															)
											| Eleftand -> expr
											| Erightand -> expr
											| Eor -> expr
											| _ -> expr2
										)
| _ -> expr2