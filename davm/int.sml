(* see report chapter 8 *)

fun smap f (cons(a,s)) = cons(f(a),fn () => smap f (force s));
type Dyadic = int list ;

fun from n = cons(n, fn()=> from(n+1));

fun f_s f = smap f (from 0);

fun s_f (cons(a,s)) 0 = a
| s_f (cons(_,s)) n = s_f (force s) (n-1);

type Real = int->int ;
datatype 'a Option = SOME of 'a | NONE ;

exception Nth ;
fun nth ([],_) = raise Nth
  | nth (h::t,0) = h
  | nth (h::t,n) = nth (t,n-1) ;

fun update NONE x = SOME x
  | update (SOME y) x = SOME (max(x,y));

fun ModMax G f =
    let val log = ref NONE
        fun f' x =
            case f x of y =>
                (log := update (!log) x ; y)
    in
        (G f', !log)
    end ;

fun zeros k = 
    if k<=0 then [] else 0::zeros(k-1) ;

(* OK for exp or not *)
fun approx_gr 0 (a:Real) = []
  | approx_gr n (a:Real) = (approx_gr (n-1) a)@[a(n-1)] ;

(* OK for exp or not *)
fun mkReal_gr (l:int list) =
    let val q = length l in
        fn n => if n<q then nth(l,n) else 0
    end ;

(* OK for exp or not *)
fun take_first 0 l = []
  | take_first n (a::l) = a::(take_first (n-1) l);

local
    fun one_o 0 = []
      | one_o k = 1::0::(one_o (k-1))
in
    fun mult_by_pow_gr (z::list) k =
	if (k mod 2 = 0) then
	    if (z + (k div 2) >= 0) then
		((z+ (k div 2))::list)
	    else
		[0]@(one_o (~z-(k div 2)))@list
	else
	    let val newlist = add_dm(0::zip_list([0,1],0::list))
		val (0::0::ans) = flip([0]@newlist@[0,0],1)
	    in
		if (z+((k+1) div 2) >= 0) then
		    ((z+((k+1) div 2))::ans)
		else
		    [0]@(one_o (~z-((k+1) div 2)))@ans
	    end
end;

fun gr_to_power k = 
    if (k >= 0) then
	if (k mod 2 = 0) then
	    [(k div 2 + 2), 1, 1,0,1]
	else
	    [(k div 2 + 2), 1, 1,1,0]
    else
	[1,1,1]@zeros((~k)-1)@[1];


(*local
fun contains_one (0::l) = contains_one l
  | contains_one [] = false
  | contains_one _ = true;
in
    fun is_gte_one (z::list) = 
	let val (sign::new_list) = flip([0]@list@[0,0],2)
	in 
	    if (sign = 0) then false
	    else if (contains_one(take_first (2*z) new_list)) 
		     then 
			 true
		 else
		     let
			 val (x::l) = flip([0]@(remove (2*z) new_list)@[0,0],2)
		     in
			 (x = 1)
		     end
	end
end; *)

fun is_gte_one list = (gr_d list >= 1.0) 
		       
fun safe_add_list(r,r') =
    let val ans = add_list(r,r') in
	if (is_gte_one ans) then NONE
	else SOME ans
    end;

local
    fun simp_2(0::list) = simp_2(list)
      | simp_2(list) = list
in
    fun simp(z::1::0::list) = if (z>0) then simp((z-1)::(rev(simp_2(rev(list)))))
			      else (z::1::0::(rev(simp_2(rev(list)))))
      | simp(list) = rev(simp_2(rev(list)))
end;

val GRDzero = [0,1,1];

fun rm_first (x::l) = (print_d x; l);

fun display' [] = ()
  | display' (0::l)  = (print "0" ; display' l)
  | display' (1::l) = (print "1" ; display' l);

fun display stack = (display' stack ; print "\n") ;

fun integrate' (F:Real -> Real) n (r:int list) (acc:int list) =
    let 
	val r_real = mkReal_gr r
	val ((z::_),_)= ModMax (fn a => approx_gr 1 (F a)) r_real
    in
	case ModMax (fn a => approx_gr (2*z+n+3) (F a)) r_real of 
	    (y,NONE) => raise BUG
	  | (y,SOME 0) => y
	  | (y,SOME k) =>
		let val acc' = add_list(acc,mult_by_pow_gr y (2*z-k))
		    and r' = add_list (r,(gr_to_power (2*z-k))) 
		in
			if (is_gte_one r') then acc'
			else 
			    integrate' F n (simp(r')) (simp(acc'))
		end  end;

fun integrate F n= (integrate' F n GRDzero GRDzero, gr_to_power (~n)) ;

fun int F n = let val (ans, error) = integrate F n in
    (gr_d(ans)-gr_d(error), gr_d(ans)+gr_d(error))
	      end;


fun FUNCTION_1 x = digit_gr 1;
fun f_F_s_1 x = s_f(FUNCTION_1(f_s(x)));

fun FUNCTION_2 x = x;
fun f_F_s_2 x = s_f(FUNCTION_2(f_s(x)));

fun FUNCTION_3 x = mult(x,x);
fun f_F_s_3 x = s_f(FUNCTION_3(f_s(x)));

fun example_5(x) = cases(x, half(), x, half());
fun FUNCTION_5 x = example_5(x);
fun f_F_s_5 x = s_f(FUNCTION_5(f_s(x)));

fun example_4(x) = cases(x, half(), half(), x);
fun FUNCTION_4 x = example_4(x);
fun f_F_s_4 x = s_f(FUNCTION_4(f_s(x)));

fun ex_1 _ = int f_F_s_1 7 ;
fun ex_2 _ = int f_F_s_2 7;
fun ex_3 _ = int f_F_s_3 3 ;
fun ex_4 _ = int f_F_s_4 5 ;
fun ex_5 _ = int f_F_s_5 5 ;



