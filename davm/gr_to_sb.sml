(* see report section 6.3 *)

fun make_exp_0_bin'(cons(z, s), n)= 
    let
	val (h1, s1) = shead_tail(force s)
	val (h2, s2) = shead_tail(s1)
    in    
	   
	if (z=0) then
	    (force s, n)
	else if (z < 0) then
		make_exp_0_bin'(cons((z+1), fn()=> cons(1, fn()=> cons(0, s))),n)
	     else
		 if ((h1=1) andalso (h2=0) andalso (z>0)) then
		     make_exp_0_bin'(cons((z-1), fn()=> s2), n) 
		 else
		     make_exp_0_bin'(divide(cons(z, s), digit_gr 2), n+1)
    end;
fun make_exp_0_bin(s)= make_exp_0_bin'(s, 0);

fun gr_to_sb'(cons(0, s)) = 
    let
	val (d2,s2)=shead_tail(force s)
    in
	if (d2 = 0) then
	    cons(~1, fn()=> gr_to_sb'(add(s2, s2, 0, 0)))
	else
	    let
		val (d3,s3)=shead_tail(s2) 
	    in
		if (d3 = 1) then
		    gr_to_sb'(cons(1, fn()=> cons(0,fn()=>cons(0,fn()=> s3))))
		    else
			cons(~1, fn()=> gr_to_sb'(cons(1, fn()=> add(s3,s3,1,0))))
	    end
    end
  | gr_to_sb'(cons(1,s)) = 
    let
	val (d2,s2)=shead_tail(force s)
    in
	if (d2 = 0) then
	    cons(0, fn()=> gr_to_sb'(add(s2, s2, 1, 0)))
	else
	    cons(1, fn()=> gr_to_sb'(add(s2, s2, 0, 0)))
    end;

fun gr_to_sb(s) = 
    let
	val (ans, exp) = make_exp_0_bin(s)
    in
	cons(exp, fn()=> gr_to_sb'(ans))
    end;

(*
fun sb_dec'([], curr)= curr
| sb_dec'(1::list, curr) =  sb_dec'(list,(curr+1.0)/2.0)
| sb_dec'(0::list, curr) = sb_dec'(list,curr/2.0)
| sb_dec'(~1::list, curr) = sb_dec'(list,(curr-1.0)/2.0);

fun sb_dec(z::list) = sb_dec'(rev(list),0.5)*power(2.0,z); 
*)
