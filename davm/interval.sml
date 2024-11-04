(* see report chapter 7 *)

fun etake 1 (cons(a,s))=[a]
  |  etake n (cons(a,s))=a :: take (n-1) (force s);

fun simplify(cons(z,s))=
    if (z=0) then 
	cons(z,s)
    else if (z<0) then
	simplify(cons((z+1), fn()=> cons(1, fn()=> cons(0,s))))
	 else
	     let
		 val (h1, s1) = shead_tail(force s)
		 val (h2, s2) = shead_tail(s1)
	     in    
		 if ((h1=1) andalso (h2=0)) then
		     simplify(cons((z-1), fn()=> s2))
		 else
		     cons(z,s)
	     end;

fun zeros k = 
    if k<=0 then [] else 0::zeros(k-1) ;

fun gr_to_power k = 
    if (k >= 0) then
	if (k mod 2 = 0) then
	    [(k div 2 + 2), 1, 1,0,1]
	else
	    [(k div 2 + 2), 1, 1,1,0]
    else
	[1,1,1]@zeros((~k)-1)@[1];

fun double_take 0 _ = ([],[])
  | double_take n (cons(a,s1), cons(b,s2)) = 
    let
	val (list1,list2) = double_take (n-1) (force s1, force s2)
    in
	(a::list1,b::list2)
    end;

fun greater_than(cons(a:int, x),cons(b:int, t)) = 
    if (a=b) then greater_than(force x, force t)
    else (a>b);

fun cases'(x,t,cons(a, y),cons(b, z)) = 
    if (a=b) then cons(a, fn()=> cases'(x,t, force y, force z))
    else
	let val ans = greater_than(x,t) in
	    if (ans = true) then cons(b, z)
	    else cons(a, y)
	end;

fun cases(x,t,y,z) = 
    let val (y',z') = lexer(y,z)
	val (x',t') = lexer(x,t) in
	    cases'(x', t', y', z')
    end;


exception NOT_10;

fun make_exp(cons(z, s), exp) =
    if (z = exp) then cons(z, s)
    else if (z<0) then
	make_exp(cons((z+1), fn()=> cons(1, fn()=> cons(0,s))), exp)
	 else
	     let
		 val (one, s2) = shead_tail(force s)
		 val (zero, s3) = shead_tail(s2)
	     in
		 if (one=1) andalso (zero=0) then 
		     make_exp(cons((z-1), fn()=> s3), exp)
		 else
		     raise NOT_10
	     end;

(*
fun interval(cons([s1,s2], rem_s), n) = 
    let
	val (s1',s2') = lexer(s1,s2)
	val s1'' = sremove n s1'
	val s2'' = sremove n s2'
    in
	common_vals(cons([s1'',s2''], rem_s), n)
    end

and common_vals(cons([s1,s2],rem_s), n) = 
    let
	val (a, s1') = shead_tail(s1)
	val (b, s2') = shead_tail(s2)
    in
	if (a=b) then cons(a, fn()=> common_vals(cons([s1',s2'], rem_s), (n+1)))
	else interval(force rem_s, n)
    end;
*)

fun all n = cons(n, fn()=> all n);

fun add_1(cons(0,s1)) = 
    let val cons(a2,s2) = force s1 in
	if (a2=0) then
	    cons(1, fn()=> cons(1,s2))
	else
	    cons(1, fn()=> cons(1, fn()=> add_1(force s2)))
    end
  | add_1(cons(0,_)) = all 1;

fun sub_1(cons(0,_)) = all 0
| sub_1(cons(1,s1)) =
  let val cons(a2, s2) = force s1 in
      if (a2=0) then
	  cons(0, fn()=> cons(0, fn()=> sub_1(force s2))) 
      else
	  cons(0, fn()=> cons(0, s2))
  end;

fun smap f (cons(a,s)) = cons(f a,fn () => smap f (force s));

fun p(0,cons(1,s)) = add_1(force s)
| p(1,cons(0,s)) = sub_1(force s)
| p(e,cons(a,s)) = if (a=e) then force s
		   else raise BUG;

fun p2 x (s1,s2) = (p(x,s1),p(x,s2));

(*fun lex_streams(cons(s1,x), cons(s2,y)) =
    let
	val (s1',s2') = lexer(s1,s2)
    in
	cons((s1',s2'), fn()=> lex_streams(force x, force y))
    end;
or *)
fun eq_exp'(cons((s1,s2),y),z) = 
    let val s1' = make_exp(s1,z)
	val s2' = make_exp(s2,z) in
	   cons((s1',s2'),fn()=>eq_exp'((force y),z))
    end;

fun eq_exp(cons((s1,s2),y)) = 
    let
	val cons(z,_) = s2
    in
	eq_exp'(cons((s1,s2),y),z)
    end;

fun lex_streams(cons((s1,s2),y)) =
    let
	val (s1',s2') = lexer(s1,s2)
    in
	cons((s1',s2'), fn()=> lex_streams((force y)))
    end;

fun common_vals(cons((s1,s2),x)) =
    let
	val cons(a, s1') = s1
	val cons(b, s2') = s2
    in
	if (a=b) then 
	    cons(a, fn()=> common_vals(cons(((force s1'),(force s2')),fn()=> (smap (p2 a) (force x)))))
	else 
	    common_vals(force x)
    end;

(* fun interval(s1,s2) = common_vals(lex_streams(s1,s2)); *)
fun interval(s) = common_vals(eq_exp(lex_streams(s)));

(*****************************************************************************)

fun exponent'(x, s_prev, sum, n) = 
    let val next_s = divide(mult(x, s_prev), digit_gr n)
	val left_int = addition(sum, next_s)
	val right_int = addition(left_int, put(gr_to_power (~n)))
    in
	cons((left_int, right_int), fn()=> exponent'(x, next_s, left_int, (n+1)))

    end;

fun exponent(x) = exponent'(x, digit_gr 1, digit_gr 1, 1);

fun sine'(x, s_prev, sum, n) = 
    let val s_next = divide(mult(x, s_prev), digit_gr ((2*n+2)*(2*n+3)))
	val s_next_again = divide(mult(x, s_next), digit_gr ((2*n+4)*(2*n+5)))
	val right_int = sub(sum, s_next)
	val left_int = addition(right_int,s_next_again)
    in
	cons((left_int, right_int), fn()=> sine'(x, s_next_again, right_int, (n+2)))

    end;

fun sine(x) = sine'(mult(x,x), x, x, 0);

fun cosine'(x, s_prev, sum, n) = 
    let val s_next = divide(mult(x, s_prev), digit_gr ((2*n+2)*(2*n+1)))
	val s_next_again = divide(mult(x, s_next), digit_gr ((2*n+4)*(2*n+3)))
	val left_int = sub(sum, s_next)
	val right_int = addition(left_int,s_next_again)
    in
	cons((left_int, right_int), fn()=> cosine'(x, s_next_again, right_int, (n+2)))

    end;

fun cosine(x) = cosine'(mult(x,x), digit_gr 1, digit_gr 1, 0);

fun log'(x, s_prev, sum, n) = 
    let val s_next = divide(mult(x, s_prev), digit_gr n)
	val new_sum = addition(s_next,sum)
	val left_int = sub(new_sum, put(gr_to_power (~n)))
	val right_int = addition(new_sum, put(gr_to_power (~n)))
    in
	cons((left_int, right_int), fn()=> log'(x, s_next, new_sum, (n+1)))

    end;

fun log(x) = log'(x, digit_gr 1, digit_gr 1, 1);





(*
fun e1'(n)= 
    let val right_int = addition(digit_gr 1, put(gr_to_power (~n))) in
	cons((digit_gr 1, right_int), fn()=> e1'((n+1)))
    end;

val e = e1'(1);

fun one_zero_zero() = cons(1,fn()=>cons(0,fn()=>cons(0, fn()=> one_zero_zero())))
fun half() = cons(1,fn()=>cons(1,fn()=>cons(1, fn()=> cons(0, fn()=>one_zero_zero()))));
val x = half();
val s_prev = digit_gr 1;
val sum =digit_gr 1;
val n = 1;

val next_s =  make_exp(divide(mult(x, s_prev), digit_gr n),2);
val next_sum =  make_exp(addition(sum, next_s),2);
val left_int = next_sum;
val right_int = make_exp(addition(left_int, put(gr_to_power (~n))),2);
val s_prev =next_s
val sum =next_sum
val n = (n+1);

fun one_zero_zero() = cons(1,fn()=>cons(0,fn()=>cons(0, fn()=> one_zero_zero())))
fun half() = cons(1,fn()=>cons(1,fn()=>cons(1, fn()=> cons(0, fn()=>one_zero_zero()))));
val e_half = exponent(half());

fun zero_one() = cons(0, fn()=> cons(1, fn()=> zero_one()));
fun one_zero_zero() = cons(1,fn()=>cons(0,fn()=>cons(0, fn()=> one_zero_zero())))
fun half() = cons(1,fn()=>cons(1,fn()=>cons(1, fn()=> cons(0, fn()=>one_zero_zero()))));


fun smin(x,y) = cases(x,y,x,y);
fun sabs(x) = cases(x, digit_gr 0, comp(x), x);

fun double_all_zero() = cons(all_zero(), fn()=> double_all_zero());
fun one_zero() = cons(1, fn()=> cons(0, fn()=> one_zero()));
fun f_one_zero() = cons(0, fn()=> one_zero());
fun double_one_zero() = cons(f_one_zero(), fn()=> double_one_zero());
fun zero_one() = cons(0, fn()=> cons(1, fn()=> zero_one()));
fun f_zero_one() = cons(0, fn()=> zero_one());
fun double_zero_one() = cons(f_zero_one(), fn()=> double_zero_one());
fun f_one() = cons(0, fn()=> cons(1, fn()=> all_zero()));
fun double_one() = cons(f_one(), fn()=> double_one());
*)
