(* see report section 5.5 *)


fun all (n) = cons(n, fn()=> all n);

fun prod2'(cons(0,alpha1), cons(beta1,beta2p), delta,gamma) = cons(delta, fn()=> 
					    prod2'((force alpha1), (force beta2p), gamma,0))
| prod2'(cons(1,alpha1), cons(beta1,beta2p), delta,gamma) = 
  let
      val cons(a2, alpha2) = force alpha1
      val cons(beta2, beta3p) = force beta2p
  in
      if (a2=0) then 
	  let val cons(h, beta12) = beta1 in
	      cons(delta, fn()=> prod2'(cons(1,alpha2), cons((force beta12),beta3p), gamma,h))
	  end
      else
	  let val cons(x, ans2) = add(beta1, cons(0, fn()=> beta2), gamma, gamma)
	      val cons(y, ans3) = force ans2
	      val cons(z, ans4) = force ans3 in
		  cons(x+delta, fn()=> prod2'(cons(1,alpha2),
				 cons((force ans4),beta3p), y,z))
	  end end;

fun prod2 (alpha, beta) = add_mk2(cons(0, fn()=> (prod2' (alpha,all beta, 0,0))));

fun smooth(cons(0, s)) = 
    let val cons(a2,s2) = force s in
	if a2 = 0 then cons(0, fn()=> smooth(force s))
	else
	    let val cons(a3,s3) = force s2 in
		if a3 = 0 then cons(0,fn()=>cons(1,fn()=>smooth(force s2)))
		else cons(1,fn()=>cons(0,fn()=>smooth(cons(0, s3))))
	    end end;

fun rearrange(cons(z,s))=
    let val cons(a1,s1) = force s in
	if a1=1 then
	    let val cons(a2,s2) = force s1 in
		if a2=1 then cons((z+1), fn()=> cons(1, fn()=> 
		             cons(1, fn()=> cons(0, fn()=> (smooth(cons(0, s2)))))))
		else 
		    cons(z,fn()=>cons(1, fn()=> smooth(force s1)))
	    end
	else 
	    cons(z, fn()=> smooth(force s))
    end;

local val one = cons(1, fn () => cons(1, fn () => all_zero())) 
in
    fun mult2(s,cons(t,s2))=
	let
	    val cons(z,s1) = rearrange(s)
	in
	    cons((z+t+3), 
		 fn () => add(add(c(add(force s1, force s2,0,0)),
				  prod2(force s1, force s2),0,1), one,1,1))
	end end;
fun one_zero_zero() = cons(1,fn()=>cons(0,fn()=>cons(0, fn()=> one_zero_zero())))
val half = cons(0, one_zero_zero);
gr_d([2,1,1]@(take 40 (prod(half,half))));
gr_to_dec(take 40 half);
