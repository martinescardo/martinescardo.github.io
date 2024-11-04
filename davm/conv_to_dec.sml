

fun dbl_l([0,0]) = []
  | dbl_l(0::0::0::list) = 0::dbl_l(0::0::list)
  | dbl_l(0::0::2::0::0::list) = 0::1::0::dbl_l(0::1::list)
  | dbl_l(0::0::2::0::2::list) = 0::1::dbl_l(0::0::3::list)
  | dbl_l(0::0::2::2::list) = 1::0::dbl_l(0::1::list)
  | dbl_l(0::0::3::0::0::list) = 0::1::1::dbl_l(0::1::list)
  | dbl_l(0::0::3::0::2::list) = 1::0::dbl_l(0::0::3::list)
  | dbl_l(0::0::3::2::list) = 1::1::dbl_l(0::0::list)
  | dbl_l(0::1::0::0::list) = 0::1::dbl_l(0::0::list)
  | dbl_l(0::1::0::2::0::0::list) = 0::1::1::0::dbl_l(0::1::list)
  | dbl_l(0::1::0::2::0::2::list) = 0::1::1::dbl_l(0::0::3::list)
  | dbl_l(0::1::0::2::2::list) = 1::0::1::dbl_l(0::0::list)
  | dbl_l(0::1::2::list) = 1::dbl_l(0::1::list)
  | dbl_l(list) = dbl_l(list@[0]);

fun add_dm([0,0]) = []
  | add_dm(0::0::0::list) = 0::add_dm(0::0::list)
  | add_dm(0::0::1::list) = 0::add_dm(0::1::list)
  | add_dm(0::0::2::0::0::list) = 0::1::0::add_dm(0::1::list)
  | add_dm(0::0::2::0::1::list) = 0::1::add_dm(0::0::2::list)
  | add_dm(0::0::2::0::2::list) = 0::1::add_dm(0::0::3::list)
  | add_dm(0::0::2::1::list) = 1::0::add_dm(0::0::list)
  | add_dm(0::0::2::2::list) = 1::0::add_dm(0::1::list)
  | add_dm(0::0::3::0::0::list) = 0::1::1::add_dm(0::1::list)
  | add_dm(0::0::3::0::1::list) = 1::0::add_dm(0::0::2::list)
  | add_dm(0::0::3::0::2::list) = 1::0::add_dm(0::0::3::list)
  | add_dm(0::0::3::1::list) = 1::add_dm(0::1::0::list)
  | add_dm(0::0::3::2::list) = 1::1::add_dm(0::0::list)
  | add_dm(0::1::0::0::list) = 0::1::add_dm(0::0::list)
  | add_dm(0::1::0::1::list) = 0::1::add_dm(0::1::list)
  | add_dm(0::1::0::2::0::0::list) = 0::1::1::0::add_dm(0::1::list)
  | add_dm(0::1::0::2::0::1::list) = 1::0::0::add_dm(0::0::2::list)
  | add_dm(0::1::0::2::0::2::list) = 0::1::1::add_dm(0::0::3::list)
  | add_dm(0::1::0::2::1::list) = 1::0::add_dm(0::1::0::list)
  | add_dm(0::1::0::2::2::list) = 1::0::1::add_dm(0::0::list)
  | add_dm(0::1::1::list) = 1::add_dm(0::0::list)
  | add_dm(0::1::2::list) = 1::add_dm(0::1::list)
  | add_dm(list) = add_dm(list@[0]);


fun zip_list([],[]) = []
  | zip_list([], list) = list
  | zip_list(list, []) = list
  | zip_list(a::list1, b::list2) = (a+b:int)::zip_list(list1,list2);

fun dbl_list(z::list) =
    let val (first_d::two_num) = zip_list(list, list)
    in
	(z+1)::dbl_l([0,0,(first_d+1)]@two_num)
    end

(*0.23606797749979*)
local
    fun one_zeros 0 = []
      | one_zeros n = 1::0::(one_zeros (n-1));
in
    fun add_list((x::s1),(y::s2))= 
	if (x=y) then 
	    let val (x1::res) = zip_list(s1,s2)
	    in
		(x+1)::add_dm([0,0,x1+1]@res)
	    end
	else if (x>y) then
	    let val (x1::res) = zip_list(s1,one_zeros(x-y)@s2) in
		(x+1)::(add_dm([0,0,x1+1]@res))
	    end
	     else
		 let val (x1::res) = zip_list(s2,one_zeros(y-x)@s1) in
		     (y+1)::(add_dm([0,0,x1+1]@res))
		 end end;
	     
fun mult_by_10 s = dbl_list (add_list(s, dbl_list(dbl_list(s))));


local
    fun set_n_one([],_) = raise BUG
      | set_n_one (a::l,0) = 1::l
      | set_n_one (a::l, n) = a::set_n_one (l, n-1)

    fun int_gr 1 = ([1],1)
      | int_gr n = 
	let val (list, exp) = int_gr (n-1) in
	    (set_n_one(flip(([0]@list@[0,0]), exp),exp),(exp+1))
	end
    
    fun complement([]) = []
      | complement(0::list) = 1::complement(list)
      | complement(1::list) = 0::complement(list)

    fun comp_fin (0::list) = comp_fin (list)
      | comp_fin (1::list) = rev(complement(list))@[1,1]

    fun comp_fin_list_1(0::list) = (1::1::0::rev(comp_fin(rev(list))))
      | comp_fin_list_1(1::0::list) = (1::0::comp_fin_list_1(list))
      | comp_fin_list_1(1::1::list) = (1::0::0::1::comp_fin(rev(list)))
      | comp_fin_list_1 list = comp_fin_list_1(list@[0]);

    fun comp_fin_list (z::list) = ((z+1)::comp_fin_list_1(list))
in
    fun negate_int 0 = [0,1,1]
      | negate_int n = 
	let
	    val (ans,exp) = int_gr n
	in
	    if (exp mod 2 = 0) then (comp_fin_list([(exp div 2)+1,1,1]@ans))
	    else (comp_fin_list([(exp div 2)+2,1,1,0]@ans))
	end
end;
(* 5 = [4,1,1,0,0,0,1,0,1,1,1,1,1];
10 = [5,1,1,0,0,0,0,1,1,1,1,0,1,1,1];
2 = [2,1,1,0,1,1,1,0,0,0]
4 = [3,1,1,0,1,0,1,0,1,0,0,0] *)


fun gr_decimal'([], _)= 0.0
  | gr_decimal'((x::list), n) = (real(x)*n)+gr_decimal'(list, n*gr);
fun gr_decimal(list) = gr_decimal'(rev(list),1.0);

fun bot x = if ((x<0.5) andalso (x>(~0.5))) then 0
	    else floor x;




(* Conversion from GR to decimal *)
(* WORKS *)
(* Input Infinate Stream with exponent as first digit *)
(* Output Stream with 0 for the exponent, n is power of 10 we 
 multiply output stream by to get same value as input*)
fun make_exp_0'(cons(z, s), n)= 
    let
	val (h1, s1) = shead_tail(force s)
	val (h2, s2) = shead_tail(s1)
    in    
	   
	if (z=0) then
	    (cons(0,s), n)
	else if (z < 0) then
	    if (z > ~4) then
		make_exp_0'(cons((z+1), fn()=> cons(1, fn()=> cons(0, s))),n)
	    else
		make_exp_0'(mult(cons(z,s), digit_gr 10), n-1)
	     else
		 if ((h1=1) andalso (h2=0) andalso (z>0)) then
		     make_exp_0'(cons((z-1), fn()=> s2), n) 
		 else
		     make_exp_0'(divide(cons(z, s), digit_gr 10), n+1)
    end;
fun make_exp_0(s)= make_exp_0'(s, 0);


(* Neg case not working *)
(* Input stream with exponent = 0
   Output Finite list with value between 0 and 1 (with no exponent), and sign of the result *)
fun flip_first_simp (cons(0, s), n) sign =
    let 
	val working_list = take n (force s)
	val (one::list) = flip([0]@(working_list)@[0,0], 1) in 
	if (one=1) then (* one=1 => value of list is positive *)
	    (working_list, sign)
	else (* one=0 => value of list is negative *)
	    flip_first_simp (comp(cons(0, s)), n) ~1
    end;

fun first 0 _ = []
| first n (a::list) = a::(first (n-1) list);

(* with new way of evaluating addition *)
(* [0,1,0,1,1,0,0,1,0,0,1,1,0,1,0,0] *)
fun simp (z::1::0::list) = simp ((z-1)::list)
  | simp list = list;

fun eval(_,~1) = ([],0)
  | eval(s,d)=
    let val s2 = mult_by_10(s)
	val (z::_)= s2
	val list = first (2*z+4) s2
	val guess_digit = bot((gr_d list))
	val s3 = simp(add_list(s2, negate_int(guess_digit)))
	val (anslist, carry)= eval(s3, d-1) 
	val next_carry = (guess_digit+carry) div 10
	val actual_digit = (guess_digit+carry) - (10*next_carry)
    in
	(anslist@[actual_digit], next_carry)
	(*(anslist@[(guess_digit,next_carry)], next_carry)*)
    end;
fun conv_to_d(stream,digits) =
    let
	val take_digits = 5*digits+4
	val (s2,exp) = make_exp_0(stream)
	val (gr_list,sign) = flip_first_simp (s2, take_digits) 1
	val (list_of_digits,n) = eval(0::gr_list, digits)
    in
	(rev(list_of_digits), exp, sign, n)
    end;

(*[0,4,9,9,3,3,8,5,3,2,9]
fun count 0 = []
| count n = (gr_d (negate_int (n)))::(count (n-1));
eval([0,1,1,1], 10);
val stream = digit_gr 5;
val digits = 10;
val take_digits = 5*digits (* not right *)
val (s2,exp) = make_exp_0(stream)
val (gr_list,sign) = flip_first_simp(s2, take_digits) 1
val s = 0::gr_list
val d = digits

val s = [0,1,1,1]
val d = 10
val s2 = mult_by_10(s)
val (z::_)= s2
val list = first (2*z+1) s2
val guess_digit = bot((gr_d list))
val s3 = simp(add_list(s2, negate_int(guess_digit)))
val s = s3
val d = d-1
*)

fun add_l([],[],a,b)=[a,b]
  | add_l(0::a,0::b,0,x) = (0::add_l(a,b,x,0))
  | add_l(0::0::a,0::b,1,x) = (0::add_l(x::a,b,1,1))
  | add_l(0::1::a,0::1::b,1,1) = (1::0::add_l(a,b,0,1))
  | add_l(0::0::a,1::0::b,1,0) = (0::1::add_l(a,b,1,0))
  | add_l(0::a,1::b,1,1) = (1::add_l(a,b,0,0))
  | add_l(1::a,1::b,1,x) = (1::add_l(a,b,x,1))
  | add_l(1::a,0::b,x,y) = add_l(0::a,1::b,x,y)
  | add_l(x::a,1::b,0,y) = add_l(x::a,0::b,1,y)
  | add_l(x1::1::a,x2::0::b,x3,y) = add_l(x1::0::a,x2::1::b,x3,y)
  | add_l(x1::y::a,x2::1::b,x3,0) = add_l(x1::y::a,x2::0::b,x3,1)
  | add_l (list1,list2,a,b) = add_l(list1@[0],list2@[0],a,b);

local
    fun one_zeros 0 = []
      | one_zeros n = 1::0::(one_zeros (n-1));
in
    fun addition_l(x::list1,y::list2) =
	if (x = y) then
	    ((x+1)::add_l(list1,list2,1,0))
	else if (x>y) then
	    add_l(x::list1, x::one_zeros(x-y)@list2, 1, 0)
	     else
		 add_l(y::one_zeros(y-x)@list1, y::list2, 1, 0)
end;

