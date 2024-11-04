type Real = int->int ;
fun top()=() and bot()=bot() ;

fun fst(x,y)=x and snd(x,y)=y ;

datatype 'a Option = SOME of 'a | NONE ;

fun compare (x:int) (y:int) =
    if x<y then LESS
    else if x=y then EQUAL
    else GREATER ;

fun member x [] = false
  | member x (y::t) = (x=y) orelse member x t ;

exception Nth ;
fun nth ([],_) = raise Nth
  | nth (h::t,0) = h
  | nth (h::t,n) = nth (t,n-1) ;
fun update fl NONE x = SOME x
  | update fl (SOME y) x = 
    if fl then SOME (max(x,y)) else SOME (min(x,y)) ;

fun ModMaxMin fl G f =
    let val log = ref NONE
        fun f' x =
            case f x of y =>
                (log := update fl (!log) x ; y)
    in
        (G f', !log)
    end ;

val ModMax = ModMaxMin true
and ModMin = ModMaxMin false ;

val Rzero     :Real = fn n => 0 ;
val Rone      :Real = fn n => 1 ;
val Rthird : Real = fn n => n mod 2 ;

type Dyadic = int list ;

val Dzero = [] ;
val Dhalf = [1] ;
val Dquarter = [1,0] ;

exception Negative ;
exception One ;

fun inc [] = raise One
  | inc (0::t) = 1::t
  | inc (1::t) = 0::(inc t) ;

fun dec [] = raise Negative
  | dec (1::t) = 0::t
  | dec (0::t) = 1::(dec t) ;

fun prune (0::t) = prune t
  | prune l      = l ;

infix eq ;
fun op eq ((r:Dyadic),(r':Dyadic)) = (prune r = prune r') ;

local
    fun mr' [] = (0.0, 1.0)
      | mr' (h::t) = 
        case mr' t of (value, error) =>
            ((real h + value)/2.0, error/2.0)
in
    fun machineReal l = mr' (rev l)
end ;


fun refine l d =
    if d=0 orelse d=1 then d::l
    else 1::dec l ;

fun approx 0 (a:Real) = Dzero
  | approx n (a:Real) = refine (approx (n-1) a) (a(n-1)) ;

fun mkReal (l:Dyadic) =
    let val q = length l in
        fn n => if n<q then nth(l,q-1-n) else 0
    end ;

fun bin_add' [] [] carry = if carry=0 then [] else raise One
  | bin_add' (d::l) (d'::l') carry =
    case d+d'+carry of t =>
        (t mod 2)::(bin_add' l l' (t div 2)) ;

fun zeros k = 
    if k<=0 then [] else 0::zeros(k-1) ;

fun bin_add r r' =
    let val (l,l') = (prune r, prune r')
        val k = length l' - length l
    in
        prune (bin_add' ((zeros k)@l) ((zeros(~k))@l') 0)
    end ;

fun safeAdd_bin r r' =
    SOME (bin_add r r')
    handle One => NONE ;

(* Dividing dyadic rationals by 2^k *)

fun scaleDown l k = l@(zeros k) ;

fun twoToMinus k = 
    if k>0 then 1::(zeros(k-1))
    else raise One ;

fun contains_one (0::l) = contains_one l
  | contains_one [] = false
  | contains_one _ = true;

(* OK for exp or not *)
fun approx_gr 0 (a:Real) = [a(0)]
  | approx_gr n (a:Real) = (approx_gr (n-1) a)@[a(n)] ;

(* OK for exp or not *)
fun mkReal_gr (l:int list) =
    let val q = length l in
        fn n => if n<q then nth(l,n) else 0
    end ;

(* OK for exp or not *)
fun take_first 0 l = []
  | take_first n (a::l) = a::(take_first (n-1) l);

(* for full notation only *)(*
local
    fun n_of a 0 = []
      | n_of a n= a::(n_of a (n-1))
in
    fun div_by_gr (z::list) k =
	let val const = 0::(n_of 1 k)
	    val new_list = (n_of 0 k)@list
	in
	    (z::add_dm(zip_list(const, new_list)))
	end
end;*)

(* simplifyed notation *)
fun div_by_gr (list) k =  zeros(k)@list;

(* for full notation only *)
(*fun gr_to_minus k = 
    if k>0 then [1,1,1]@zeros(k-1)@[1]
    else raise BUG;
	*)
(* simplifyed notation *)
fun gr_to_minus k = zeros(k-1)@[1];

(* full notation only *)(*
fun is_gte_one (z::list) = let val (sign::new_list) = flip([0]@list@[0,0],1)
		       in 
			   if (sign = 0) then false
			   else if 
			       (contains_one(take_first (2*z) new_list)) then true
				else
				    let
					val (x::l) = flip([0]@(remove (2*z) new_list)@[0,0], 1)
				    in
					(x = 1)
				    end
		       end;*)

(* simplifyed notation *)
fun is_gte_one (list) = 
    let val (sign_1::sign_2::new_list) = flip(list@[0,0],1)
    in 
	if (sign_1 <> 0) orelse (sign_2<>0) then NONE
	else SOME new_list
    end;



fun safe_add_list(r,r') =
    let val ans = add_dm([0,0]@zip_list(r,r')) 
    in (* add_list(r,r') for full notation *)
	is_gte_one ans
    end;

fun safe_add_list_r(r,r') =
    let val ans = add_dm([0,0]@zip_list(r,r')) 
	val SOME ans_2 = is_gte_one ans
	val (sign::ans_3) = flip([0]@ans_2@[0,0],1)
    in
	if (sign = 1) then
	    NONE
	else 
	    SOME ans_2
    end;

(* ORIGIONAL *)
(*fun integrate' (F:Real->Real) n (r:Dyadic) (acc:Dyadic) =
    case ModMax (fn a => approx n (F a)) (mkReal r) of 
        (y,NONE) => y
      | (y,SOME k) =>
            let val SOME acc' = add acc (scaleDown y (k+1))
                and r' = safeAdd r (twoToMinus(k+1))
            in
                case r' of
                    NONE     => acc'
                  | SOME r'' => integrate' F n r'' acc'
                                (* this is tail-recursive *)
            end ;
*)

(* CURRENT *)
fun integrate' (F:Real -> Real) n (r:int list) (acc:int list) =
    case ModMax (fn a => approx_gr n (F a)) (mkReal_gr r) of 
        (y,NONE) => y
      | (y,SOME k) =>
	    let val SOME acc' = safe_add_list(acc,div_by_gr y k)
                and r' = safe_add_list_r(r,(gr_to_minus k))
            in
                case r' of
                    NONE     => acc'
                  | SOME r'' => integrate' F n r'' acc'
                                (* this is tail-recursive *)
            end ;
	

val GRDzero = [0]; (* should be [0,1,1] *)
fun integrate F n = (integrate' F n GRDzero GRDzero, gr_to_minus n) ;

fun smap f (cons(a,s)) = cons(f(a),fn () => smap f (force s));

fun FUNCTION x = prod(x,x)

fun f_s f = smap f (from 0);

fun s_f (cons(a,s)) 0 = a
| s_f (cons(_,s)) n = s_f (force s) (n-1);

fun id x = x ;
integrate id 10;
val (x,y) = it; val w = 1::1::1::y; val z = 1::1::1::x; gr_d z; gr_d w;
















fun integrate' (F:Real -> Real) n (r:int list) (acc:int list) =
    let 
	val r_real = (fn()=> put r) in
	    case ModMax (fn a => take n (F a)) (r_real r) of 
		(y,~2) => y
	      | (y,~1) => y
	      | (y,k) =>
		    let val SOME acc' = safe_add_list(acc,div_by_gr y (k+1))
			and r' = safe_add_list_r(r,(gr_to_minus (k+1)))
		    in
			case r' of
			    NONE     => acc'
			  | SOME r'' => integrate' F n r'' acc'
		    (* this is tail-recursive *)
		    end end;
