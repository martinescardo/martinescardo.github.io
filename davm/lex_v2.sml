(* Bad algorithm that works *)
fun half() = cons(1, fn() => cons(0,fn()=> cons(0, fn()=> half())));

fun first_st(cons((a::_::[1]), s1)) = (cons(a, fn()=> first_st(force s1)))
  | first_st(cons((_::b::[~1]), s1)) = (cons(b, fn()=> first_st(force s1)));

fun second_st(cons((_::b::[1]), s1)) = (cons(b, fn()=> second_st(force s1)))
  | second_st(cons((a::_::[~1]), s1)) = (cons(a, fn()=> second_st(force s1)));

fun dbl_list(cons(a,s1),cons(b,s2),switch) = ((cons([a,b,switch], fn()=> 
						    dbl_list(force s1,force s2,switch))));


fun lex_n(s1,s2,switch,0) = dbl_list(s1,s2,switch)
  | lex_n(cons(0,s1),cons(0,s2),switch,n) = 
	(cons([0,0,switch], fn () => (lex_n(force s1, force s2,switch,(n-1)))))
  | lex_n(cons(1,s1),cons(1,s2),switch,n) = 
	(cons([1,1,switch], fn () => (lex_n(force s1, force s2,switch,(n-1)))))
  | lex_n(cons(0,s1),cons(1,s2),switch,n) = 
    let
	val (a1,s12)=shead_tail(force s1)
	val (b1,s22)=shead_tail(force s2)
	val (a2,s13)=shead_tail(s12)
	val (b2,s23)=shead_tail(s22)
    in
	if ((a1=0) andalso (b1=1)) then 
	    (cons([0,1,switch], fn ()=> dbl_list(force s1,force s2,switch)))
	else if (a1=b1) then
	    if ((a2=0) orelse (b2=1)) then
		(cons([0,1,switch], fn ()=> dbl_list(force s1,force s2,switch)))
	    else if (a1=1) then 
		(cons([1,1,switch], fn () => (lex_n(cons(0,fn() => cons(0, fn () => s13)),force s2,switch,(n-1)))))
		 else 
		     (cons([0,0,switch], fn () => (lex_n(force s1,cons(1,fn()=>cons(1,fn() => s23)),switch,(n-1)))))
	     else
		 if (a2=b2) then 
		     if (a2=1) then 
			 (cons([1,1,switch], fn () => cons([0,0,switch],fn()=>(lex_n(cons(0,fn()=> s13), s22,switch,(n-2))))))
		     else 
			 (cons([0,0,switch], fn () => 
			       cons([1,1,switch],fn()=>(lex_n(s12,cons(1,fn() => s23),switch,(n-2))))))
		 else if ((a2=1) andalso (b2=0)) then
		     (cons([1,1,switch], fn () => 
			   cons([0,0,switch], fn() => cons([0,0,switch], fn () => (lex_n(s13,s23,switch,(n-3)))))))
		      else
			  (cons([0,1,switch], fn ()=> dbl_list(force s1,force s2,switch)))
    end
  | lex_n(cons(1,s2),cons(0,s1),switch,n) = lex_n(cons(0,s1),cons(1,s2),(~1*switch),n);
fun compare(cons(0,s1),cons(0,s2))=compare(force s1, force s2)
  | compare(cons(1,s1),cons(1,s2))=compare(force s1, force s2)
  | compare(cons(1,s1),cons(0,s2))= GREATER
  | compare(cons(0,s1),cons(1,s2))= LESS;

fun bin(_,0) = []
  | bin (list, d) = 
    let
	val l = length(list)
	val lex_st = first_st(lex_n(put list, half(), 1, l)) 
	(* apply lexer at max l times*)
	val inter = compare(lex_st, half())
	(* find in which interval list is *)
	val lex_list = take (l+2) lex_st
	val two_lex_list = add_l(lex_list,lex_list,0,0)
	(* find 2 * list *)
	val fliped_two_list = flip([0]@two_lex_list,1)
	val new_list = cut_end(remove 3 fliped_two_list)
    in
	if (inter = LESS) then
	    0::bin(new_list, d-1)
	else (*inter = GREATER *)
	    1::bin(new_list, d-1)
    end;
