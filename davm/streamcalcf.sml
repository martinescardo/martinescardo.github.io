datatype 'a stream = cons of 'a * (unit -> 'a stream);
fun force s = s();


exception BUG;

datatype Order = LESS | EQUAL | GREATER ;

(****************************************************************************)
(* general functions *)

fun shead_tail(cons(h,s))=(h, force s);

fun simplify(cons(z,s))=
    if (z<=0) then
	cons(z,s)
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

fun remove 0 l = l
  | remove n (_::l)= remove (n-1) l
  | remove _ [] = raise BUG;

fun sremove 0 s = s
  | sremove n (cons(a,s)) = sremove (n-1) (force s);

fun more list = remove 12 list;

fun take 1 (cons(a,_))=[a]
 |  take n (cons(a,s))=a :: take (n-1) (force s);

fun all_zero() = cons(0, fn () => all_zero());

fun put [] = all_zero()
  | put (d::list) = cons(d, fn () => (put list));

fun double_take 0 _ = ([],[])
  | double_take n (cons(a,s1), cons(b,s2)) = 
    let
	val (list1,list2) = double_take (n-1) (force s1, force s2)
    in
	(a::list1,b::list2)
    end;

fun double_more (list1,list2) = (remove 12 list1,remove 12 list2) ;

val gr = (1.0+sqrt(5.0))/2.0;

fun first (a,_)=a;

fun second (_,a)=a;

fun power(x,k):real = 
    if k=0 then 1.0
	else if k<0 then power((1.0)/x, ~k)
	     else if k=1 then x
		  else if k mod 2 = 0 then power(x*x, k div 2)
		       else x*power(x*x, k div 2);
	     
(*convert from GR to decimal *)
fun gr_dec([], res, _)= res
  | gr_dec((x::list), sub_tot, n) = gr_dec(list, sub_tot+(real(x)*n), n/gr);

fun gr_to_dec (alist)= gr_dec(alist, real(0), real(1)/gr);

(*convert from GR (full notation) to decimal *)
fun gr_d (n::alist)= 
    (((gr_dec(alist, real(0), (1.0/gr))-1.0)*(power(gr,(2*n)))))
  | gr_d [] = raise BUG;

(**************************************************************************)
(* code for flip *)
fun n_ones(0)=[]
| n_ones(n)=(1::n_ones(n-1));

fun even_seq(0)=[0]
  | even_seq(1)=raise BUG
  | even_seq(n)=(1::0::even_seq(n-2));

fun is_even(n)= (n mod 2 = 0);

fun head_tail([])= raise BUG
  | head_tail(x::l)=(x,l);

    
fun flip'(0::alist,1,n) = [0]@n_ones(n)@[0]@alist          (* 0 1^n *0* alist *)
  | flip'(0::alist,d,n) = [0]@n_ones(n)@flip'(alist,d-1,0) (* 0 1^n 0 *alist* *)
  | flip'(1::alist,1,n) = 
    if is_even(n+1) then even_seq(n+1)@alist               (* 0 1^2p-1 *1* alist *)
    else
	let
	    val (x,l)=head_tail(alist)
	in
	    if x=1 then even_seq(n+2)@l                    (* 0 1^2p *1* 1 0 l *)
	    else 
		let 
		    val (y::0::m)=(flip(alist,2))
		in
		    if (y = 0) then
			[0]@n_ones(n)@[0,1,1]@m            (* 0 1^2p *1* 0 0 m *)
		    else
			even_seq(n+2)@[0]@m                  (* 0 1^2(p+1) *1* 1 0 m *)
		end
	end
  | flip'(1::alist,d,n) = flip'(alist,d-1,n+1)
  | flip' _ = raise BUG

and flip(0::alist,1) = (0::alist)
  | flip(0::alist,d) = flip'(alist,d-1,0)
  | flip(1::alist,_) = raise BUG;

(******************************************************************)

fun normalise(cons(x,s1),cons(y,s2))=
    if (x=y) then 
	(cons(x,s1),cons(y,s2))
    else 
	if (x<y) then
	    normalise(cons((x+1), fn () => 
			  cons(1, fn () => 
			       cons(0, fn () => force s1))), 
		     cons(y,s2))
	else
	    normalise(cons(x,s1), 
		     cons((y+1), fn () => 
			  cons(1, fn () => 
			       cons(0, fn () => 
				    force s2))));
    
    
(* code for basic operations *)
(****************************************************************************)
(* ADDITION *)
(*fun add_l([],[],a,b)=[a,b]
| add_l(0::a,0::b,0,x) = (0::add_l(a,b,x,0))
  | add_l(0::0::a,0::b,1,x) = (0::add_l(x::a,b,1,1))
  | add_l(0::1::a,0::1::b,1,1) = (1::0::add_l(a,b,0,1))
  | add_l(0::0::a,1::0::b,1,0) = (0::1::add_l(a,b,1,0))
  | add_l(0::a,1::b,1,1) = (1::add_l(a,b,0,0))
  | add_l(1::a,1::b,1,x) = (1::add_l(a,b,x,1))
  | add_l(1::a,0::b,x,y) = add_l(0::a,1::b,x,y)
  | add_l(x::a,1::b,0,y) = add_l(x::a,0::b,1,y)
  | add_l(x1::1::a,x2::0::b,x3,y) = add_l(x1::0::a,x2::1::b,x3,y)
  | add_l(x1::y::a,x2::1::b,x3,0) = add_l(x1::y::a,x2::0::b,x3,1); *)

fun add(cons(0,a),cons(0,b),0,y) = cons(0, fn () => add(force a,force b,y,0))
  | add(cons(0,a),cons(1,b),1,1) = cons(1, fn () => add(force a,force b,0,0))
  | add(cons(1,a),cons(1,b),1,y) = cons(1, fn () => add(force a,force b,y,1))
  | add(cons(1,a),cons(0,b),x,y) = add(cons(0,a),cons(1,b),x,y)
  | add(cons(x,a),cons(1,b),0,y) = add(cons(x,a),cons(0,b),1,y)
  | add(cons(x11,a),cons(x21,b),x,y) =
    let 
	val (x12,a2)=shead_tail(force a)
	val (x22,b2)=shead_tail(force b)
    in
	if ((x11=0) andalso (x12=0) andalso (x21=0) andalso (x=1)) then
	    cons(0,fn () => add(cons(y,fn () => a2), force b,1,1))

	else if ((x11=0) andalso (x12=1) andalso (x21=0) andalso (x22=1) andalso (x=1) andalso (y=1)) then
	    cons(1,fn () => cons(0,fn () => add(a2,b2,0,1)))
	     else if ((x11=0) andalso (x12=0) andalso (x21=1) andalso (x22=0) andalso (x=1) andalso (y=0)) then
		 cons(0,fn () => cons(1,fn () => add(a2,b2,1,0)))

		  else if ((x12=1) andalso (x22=0)) then
		      add(cons(x11,fn () => cons(0,fn () => a2)),
			  cons(x21,fn () => cons(1,fn () => b2)),x,y)
		      else if ((x22=1) andalso (y=0)) then
			  add(cons(x11,fn () => cons(x12,fn () => a2)),
			      cons(x21,fn () => cons(0,fn () => b2)),x,1)
			   else raise BUG
			       
    end;

fun addition(cons(x,s1),cons(y,s2))= 
    if (x=y) then 
	cons((x+1),fn () => add(force s1,force s2,1,0))
    else 
	let
	    val (cons(nx,ns1),cons(ny,ns2))=normalise(cons(x,s1),cons(y,s2))
	in
	    addition(cons(nx,ns1),cons(ny,ns2))
	end;

(*****************************************************************************)	
(* NEW ADDITION *)
fun zip (cons(a,s1), cons(b,s2)) = 
    cons((a+b):int, fn() => zip(force s1, force s2));

fun two_zip (cons(a,s)) = 
    cons((a+a):int, fn() => two_zip(force s));

local
    fun dbl (cons(0, s)) = 
	let val (x1,s2)=shead_tail(force s) val (x2,s3)=shead_tail(s2) in
	    if (x1=0) then (* 00 *)
		if (x2=0) then (* 000 => 0!00 *)
		    cons(0, fn()=> (dbl (force s)))
		else if (x2=2) then (* 002 *)
		    let val (x3,s4)=shead_tail(s3) in
			if (x3=2) then (* 0022 => 10!01 *)
			    cons(1, fn() => cons(0, fn() => dbl (cons(0, fn()=> cons(1, fn() => s4)))))
			else
			    let val (x4,s5)=shead_tail(s4) in
				if (x4=2) then (* 00202 => 01!003 *)
				    cons(0, fn() => cons(1, fn() =>
							 dbl (cons(0, fn()=> cons(0, fn()=> cons(3, fn()=>s5))))))
			    else (* 00200 => 010!01 *)
				cons(0, fn() => cons(1, fn() => cons(0, fn() =>
					dbl (cons(0, fn()=> cons(1, fn()=> s5))))))
			end end
		 else (* 003 *)
		     let val (x3,s4)=shead_tail(s3) in
			 if (x3=0) then (* 0030 *)
			     let val (x4,s5)=shead_tail(s4) in
				 if (x4=0) then (* 00300 => 011!01 *)
				     cons(0, fn()=> cons(1, fn()=> cons(1, fn() => 
									dbl(cons(0,fn()=> cons(1, fn()=>s5))))))
				 else (* 00302 => 10!003 *)
				     cons(1, fn()=> cons(0, fn()=>
							 dbl(cons(0,fn()=> cons(0,fn()=> cons(3, fn()=>s5))))))
			     end
			 else (* 0032 => 11!00 *)
			     cons(1, fn()=> cons(1, fn()=>
						 dbl(cons(0,fn()=> cons(0, fn()=>s4)))))
		     end
	else (* 01 *)
	    let val (x2,s3)=shead_tail(s2) in
		if (x2=2) then (* 012 => 1!01 *)
		    cons(1, fn()=> dbl(cons(0, fn()=> cons(1,fn()=>s3))))
		else (* 010 *)
		    let val (x3,s4)=shead_tail(s3) in
			if (x3=0) then (* 0100 => 01!00 *)
			    cons(0, fn()=> cons(1, fn()=>
						dbl(s2)))
			else
			    let val (x4,s5)=shead_tail(s4) in
				if (x4=2) then (* 01022 => 101!00 *)
				    cons(1, fn()=> cons(0, fn()=> cons(1, fn()=> 
								       dbl(cons(0, fn()=> cons(0, fn()=>s5))))))
				else
				    let val (x5,s6)=shead_tail(s5) in
					if (x5=0) then (* 010200 => 0110!01 *)
					   cons(0, fn()=> cons(1, fn()=> cons(1, fn()=> cons(0, fn()=> 
						dbl(cons(0, fn()=> cons(1, fn()=>s6)))))))
					else (* 010202 => 011!003 *)
					    cons(0, fn()=> cons(1, fn()=> cons(1, fn()=> 
						dbl(cons(0, fn()=> cons(0, fn()=> cons(3, fn()=>s6)))))))
				    end end end end end
  | dbl _ = raise BUG;
in

    fun double(cons(z,s))= 
	    let val two_num = two_zip(force s)
		val cons(x1,s1) = two_num
	    in
		cons((z+1),fn () => 
		     dbl(cons(0, fn()=> 
			      cons(0, fn()=> 
				   cons(x1+1, s1)))))
	    end
end;


fun add_mk2 (cons(0, s)) = 
    let val (x1,s2)=shead_tail(force s) val (x2,s3)=shead_tail(s2) in
	if (x1=0) then (* 00 *)
	    if (x2=0) then (* 000 => 0!00 *)
		cons(0, fn()=> (add_mk2 (force s)))
	    else if (x2=1) then (* 001 => 0!01 *)
		cons(0, fn()=> (add_mk2 (force s)))
	    else if (x2=2) then (* 002 *)
		let val (x3,s4)=shead_tail(s3) in
		    if (x3=2) then (* 0022 => 10!01 *)
			cons(1, fn() => cons(0, fn() => add_mk2 (cons(0, fn()=> cons(1, fn() => s4)))))
		    else if (x3=1) then (* 0021 => 10!00 *)
			cons(1, fn() => cons(0, fn() => add_mk2 (cons(0, fn()=> cons(0, fn() => s4)))))
			 else
			     let val (x4,s5)=shead_tail(s4) in
				 if (x4=2) then (* 00202 => 01!003 *)
				     cons(0, fn() => cons(1, fn() =>
							  add_mk2 (cons(0, fn()=> cons(0, fn()=> cons(3, fn()=>s5))))))
				 else if (x4=1) then (* 00201 => 01!002 *)
				     cons(0, fn() => cons(1, fn() =>
							  add_mk2 (cons(0, fn()=> cons(0, fn()=> cons(2, fn()=> s5))))))
				      else (* 00200 => 010!01 *)
					  cons(0, fn() => cons(1, fn() => cons(0, fn() =>
					    add_mk2 (cons(0, fn()=> cons(1, fn()=> s5))))))
			     end end
		 else (* 003 *)
		     let val (x3,s4)=shead_tail(s3) in
			 if (x3=0) then (* 0030 *)
			     let val (x4,s5)=shead_tail(s4) in
				 if (x4=0) then (* 00300 => 011!01 *)
				     cons(0, fn()=> cons(1, fn()=> cons(1, fn() => 
									add_mk2(cons(0,fn()=> cons(1, fn()=>s5))))))
				     else if (x4=1) then (* 00301 => 10!002 *)
					 cons(1, fn()=> cons(0, fn()=>
							     add_mk2(cons(0,fn()=> cons(0,fn()=> cons(2, fn()=>s5))))))
					  else (* 00302 => 10!003 *)
					      cons(1, fn()=> cons(0, fn()=>
						add_mk2(cons(0,fn()=> cons(0,fn()=> cons(3, fn()=>s5))))))
			     end
			 else if (x3=1) then (* 0031 => 1!010 *)
			     cons(1, fn()=> add_mk2(cons(0,fn()=> cons(1,fn()=> cons(0, fn()=>s4)))))
			      else (* 0032 => 11!00 *)
				  cons(1, fn()=> cons(1, fn()=>
						      add_mk2(cons(0,fn()=> cons(0, fn()=>s4)))))
		     end
	else (* 01 *)
	    let val (x2,s3)=shead_tail(s2) in
		if (x2=2) then (* 012 => 1!01 *)
		    cons(1, fn()=> add_mk2(cons(0, fn()=> cons(1,fn()=>s3))))
		else if (x2=1) then (* 011 => 1!00 *)
		    cons(1, fn()=> add_mk2(cons(0, fn()=> cons(0,fn()=>s3))))
		else (* 010 *)
		    let val (x3,s4)=shead_tail(s3) in
			if (x3=0) then (* 0100 => 01!00 *)
			    cons(0, fn()=> cons(1, fn()=> add_mk2(s2)))
			    else if (x3=1) then (* 0101 => 01!01 *)
				cons(0, fn()=> cons(1, fn()=> add_mk2(s2)))
				 else
				     let val (x4,s5)=shead_tail(s4) in
					 if (x4=2) then (* 01022 => 101!00 *)
					     cons(1, fn()=> cons(0, fn()=> cons(1, fn()=> 
						add_mk2(cons(0, fn()=> cons(0, fn()=>s5))))))
					 else if (x4=1) then (* 01021 => 10!010 *)
					     cons(1, fn()=> cons(0, fn()=> 
						 add_mk2(cons(0, fn()=>cons(1, fn()=>cons(0, fn()=> s5))))))
					 else
					     let val (x5,s6)=shead_tail(s5) in
						 if (x5=0) then (* 010200 => 0110!01 *)
						     cons(0, fn()=> cons(1, fn()=> cons(1, fn()=> cons(0, fn()=> 
							add_mk2(cons(0, fn()=> cons(1, fn()=>s6)))))))
						 else if (x5=1) then (* 01201 => 100!002 *)
						      cons(1, fn()=> cons(0, fn()=> cons(0, fn()=> 
						       add_mk2(cons(0, fn()=> cons(0, fn()=> cons(2, fn()=>s6)))))))
						      else (* 010202 => 011!003 *)
							  cons(0, fn()=> cons(1, fn()=> cons(1, fn()=> 
							  add_mk2(cons(0, fn()=> cons(0, fn()=> cons(3, fn()=>s6)))))))
					     end end end end end
  | add_mk2 _ = raise BUG; 


fun addition_mk2(cons(x,s1),cons(y,s2))= 
    if (x=y) then 
	let val num = zip(force s1,force s2)
	    val cons(x1,res) = num
	in
	    cons((x+1),fn () => 
		 add_mk2(cons(0, fn()=>
			      cons(0, fn()=>
				   cons(x1+1, res)))))
	end
    else 
	let
	    val (cons(nx,ns1),cons(ny,ns2))=normalise(cons(x,s1),cons(y,s2))
	in
	    addition_mk2(cons(nx,ns1),cons(ny,ns2))
	end;


(****************************************************************************)
(* COMPEMENT *)
fun c(cons(1,s)) = cons(0,fn () => c(force s))
      | c(cons(0,s)) = cons(1,fn () => c(force s))
  | c(_) = raise BUG;

fun comp_1 (cons(0,s))= cons(1, fn () => cons(1, fn () => cons(0, fn () => c(force s))))
  | comp_1 (cons(1,s))=
    let
	val (x2,s2)=shead_tail(force s)
    in
	if (x2=0) then 
	    cons(1, fn () => cons(0, fn () => comp_1(s2)))
	else
	    cons(1, fn () => cons(0, fn () => cons(0, fn () => cons(1, fn () => c(s2)))))
	    
    end
  | comp_1 (_) = raise BUG;
    
fun comp(cons(z,alist))= cons((z+1), fn () => comp_1 (force alist));
    	    
(*SUBTRACTION *)
fun sub(cons(x,s1),cons(y,s2))=
    if (x=y) then 
	cons((x+1),fn () => (add(force s1,c(force s2),1,1)))
    else 
	     let
		 val (cons(nx,ns1),cons(ny,ns2))=normalise(cons(x,s1),cons(y,s2))
	     in
		 sub(cons(nx,ns1),cons(ny,ns2))
	     end;
	     
(****************************************************************************)
(* MULTIPLICATION *)
(*fun prod(0::a,b)=(0::prod(a,b))
  | prod(a,0::b)=(0::prod(a,b))
  | prod(1::0::a,1::0::b)=(0::add(add(a,b,0,0),0::prod(a,b),1,0))
  | prod(1::1::a,1::0::b)=(add(add(0::a,b,0,0),0::0::prod(a,b),1,0))
  | prod(1::0::a,1::1::b)=(add(add(a,0::b,0,0),0::0::prod(a,b),1,0))
  | prod(1::1::a,1::1::b)=(add(add(a,b,0,0),0::0::prod(a,b),1,1));*)
        
fun prod(a,cons(0,b)) = cons(0, fn () => (prod(a, force b)))  
| prod(cons(0,a),b) = cons(0, fn () => prod(force a, b))
  | prod(cons(1,a),cons(1,b))=
    let 
	val (x12,a2)=shead_tail(force a)
	val (x22,b2)=shead_tail(force b)
    in
	if (x22=0) then
	    if (x12=0) then 
		cons(0,fn () => add(add(a2,b2,0,0),
				    cons(0,fn () => prod(a2,b2)),1,0)) (*00*)
	    else
		(add(add(cons(0,fn () => a2), b2,0,0),
		     cons(0, fn () => cons(0, fn () => prod(a2,b2))),1,0)) (*10*)
	else if (x12=0) then 
	    (add(add(a2,cons(0,fn () => b2),0,0),
		 cons(0,fn () => cons(0,fn () => prod(a2,b2))),1,0)) (*01*)  
	     else
		 (add(add(a2,b2,0,0),
		      cons(0, fn () => cons(0,fn () => prod(a2, b2))),1,1)) (*11*)
    end
  | prod _  = raise BUG;
    
local
    val one = cons(1, fn () => cons(1, fn () => all_zero()))
in
    fun mult(cons(z,s1),cons(t,s2))= 
	cons((z+t+3), 
	     fn () => add(add(c(add(force s1, force s2,0,0)),
			      prod(force s1, force s2),0,1), one,1,1))
end;

(****************************************************************************)
(* DIVIDE *)
(*fun div_1(0::0::a,b)=div_2(add(a,0::b,0,0),0::a,b)
  | div_1(0::1::a,b)=div_2(add(a,0::b,1,1),1::a,b)
  | div_1(1::0::a,b)=div_2(add(a,1::b,1,1),a,b)

and div_2(0::0::c,a,b)=(0::div_1(a,b))
  | div_2(0::1::0::c,a,b)=(0::div_1(a,b))
  | div_2(0::1::1::c,a,b)=(1::div_1(0::0::c,b))
  | div_2(1::c,a,b)=(1::div_1(c,b));

fun divide(a,1::b)=div_1(0::0::a,c(b));*)

fun D_1(cons(0,s1), s2) = 
    let
	val (x12,s12)=shead_tail(force s1)
    in
	if (x12=0) then
	    D_2(add(s12,cons(0, fn() => s2),0,0), cons(0, fn () => s12), s2)
	else
	    D_2(add(s12,cons(0, fn() => s2),1,1), cons(1, fn () => s12), s2)
    end
  | D_1(cons(1,s1), s2)=
    let
	val (x12,s12)=shead_tail(force s1)
    in
	if (x12 = 0) then
	    D_2(add(s12,cons(1, fn () => s2),1,1),s12, s2)
	else
	    raise BUG
    end
  | D_1 _ = raise BUG

and D_2(cons(0,s3),s1,s2)=
    let
	val (x32,s32)=shead_tail(force s3)
	val (x33,s33)=shead_tail(s32)
    in
	if (x32=0) then
	    cons(0, fn () => D_1(s1, s2))	
	else if (x33=0) then 
	    cons(0, fn () => D_1(s1, s2))
	     else
		 cons(1, fn () => D_1(cons(0,fn()=> cons(0, fn () => s33)), s2))
    end
| D_2(cons(1,s3),s1,s2) = cons(1, fn () => D_1(force s3, s2))
| D_2 _ = raise BUG;


fun D(a,cons(1,b))= D_1(cons(0, fn () => cons(0, fn () => a)), (c(force b)))
  | D _ = raise BUG;

(* 
D'(z:a,t:0:b)=D'_1(C'((z-t):a),0:C(b))
| D'(z:a,t:1:0:b)=D'(z:a,(t-1):b)
| D'(z:a,t:1:1:b)=D'_1((z-t+1):a,b)

D'_1(z:a,0:0:b)=D'_1((z+1):a,b)
| D'_1(z:a,0:1:b)=(z+1):D_1(A(a,b,0,0),C(b))
| D'_1(z:a,1:b)=(z+1):D_1(A(0:a,b,0,1),C(b))
*)
fun divide(cons(z,s1),cons(t,s2)) = 
    let
	val (x22,s22)=shead_tail(force s2)
	val (x23,s23)=shead_tail(s22)
    in
	if (x22=0) then
	    divide_1(comp(cons((z-t),s1)),cons(0, fn () => c(s22)))
	else if (x23=0) then
	    divide(cons(z, s1), cons((t-1), fn () => s23))
	    else
		divide_1(cons((z-t+1),s1), s23)
    end
    
and divide_1(cons(z,s1), cons(1,s2)) =  cons((z+1), fn () => 
					     D_1(add(cons(0, s1), 
						     force s2,0,1), c(force(s2))))
  | divide_1(cons(z,s1), cons(0,s2))=
    let
	val (x22,s22)=shead_tail(force s2)
    in
	if (x22=0) then
	    divide_1(cons((z+1), s1), s22)
	else 
	    cons((z+1), fn () => D_1(add(force s1, s22, 0,0), c(s22)))
    end
  | divide_1 _ = raise BUG;

(****************************************************************************)
(*
fun lex(a::x,a::y) = a::lex(x,y)
  | lex(0::a1::a2::x, 1::b1::b2::y) = 
    if ((a1=0) andalso (b1=1)) then                     [we have (00(a2)x,11(b2)y)]
	(0::0::a2::x, 1::1::b2::y)                        [since 00(a2)x < 11(b2)y]
    else if (a1=b1) then                               [we have (0n(a2)x, 1n(b2)y)]
	if (a2=0 orelse b2=1) then            [we have (0n0x, 1n?y) or (0n?x,1n1y)]
	    (0::a1::a2::x, 1::b1::b2::y)         [since 0n0x < 1n?y or 0n?x < 1n1y]
	    else if (a1=1) then                               [we have (011x,110y)]
		1::lex(0::1::x,1::0::y)                         [since 011x = 100x]
		 else                                         [we have (001x,100y)]
		     0::lex(0::1::x, 1::1::y)                   [since 100y = 011y]
	 else                                           [we have (01(a2)x,10(b2)y)]
	     if (a2=b2) then                                  [we have (01nx,10ny)]
		 if (a2=1) then                               [we have (011x,100y)]
		     1::0::lex(0x,1y)                           [since 011x = 100x]
		 else                                         [we have (010x,100y)]
		     0::1::lex(0x,1y)                           [since 100y = 011y]
	else if ((a2=1) andalso (b2=0)) then                  [we have (011x,100y)]
	    1::0::0::lex(x,y)                                   [since 011x = 100x]
	     else                                             [we have (010x,101y)]
		 (010x,101y)                                    [since 010x < 101y]
*)

(*SHORTER LEXER*)
fun dbl_list(cons(a,s1),cons(b,s2),switch) = ((cons([a,b,switch],  fn()=> dbl_list(force s1,force s2,switch))));


fun lex(cons(0,s1),cons(0,s2),switch) = 
	(cons([0,0,switch], fn () => (lex(force s1, force s2,switch))))
  | lex(cons(1,s1),cons(1,s2),switch) = 
	(cons([1,1,switch], fn () => (lex(force s1, force s2,switch))))
  | lex(cons(0,s1),cons(1,s2),switch) = 
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
		(cons([1,1,switch], fn () => 
		      (lex(cons(0,fn() => cons(0, fn () => s13)),force s2,switch))))
		 else 
		     (cons([0,0,switch], fn () => 
			   (lex(force s1,cons(1,fn()=>cons(1,fn() => s23)),switch))))
	     else
		 if (a2=b2) then 
		     if (a2=1) then 
			 (cons([1,1,switch], fn () => 
			       cons([0,0,switch],fn()=>
				    (lex(cons(0,fn()=> s13), s22,switch)))))
		     else 
			 (cons([0,0,switch], fn () => 
			       cons([1,1,switch],fn()=>
				    (lex(s12,cons(1,fn() => s23),switch)))))
		 else if ((a2=1) andalso (b2=0)) then
		     (cons([1,1,switch], fn () => 
			   cons([0,0,switch], fn() => 
				cons([0,0,switch], fn () => (lex(s13,s23,switch))))))
		      else
			  (cons([0,1,switch], fn ()=> dbl_list(force s1,force s2,switch)))
    end
  | lex(cons(1,s2),cons(0,s1),switch) = lex(cons(0,s1),cons(1,s2),(~1*switch))
  | lex _ = raise BUG;


fun first_st(cons((a::_::[1]), s1)) = (cons(a, fn()=> first_st(force s1)))
  | first_st(cons((_::b::[~1]), s1)) = (cons(b, fn()=> first_st(force s1)))
  | first_st _ = raise BUG;
    
fun second_st(cons((_::b::[1]), s1)) = (cons(b, fn()=> second_st(force s1)))
  | second_st(cons((a::_::[~1]), s1)) = (cons(a, fn()=> second_st(force s1)))
  | second_st _ = raise BUG;

(*THIS WORKS FOR THE ABOVE LEXER*)
fun lexer(s1,s2)=
    let
	val (cons(z,ns1),cons(t,ns2)) = normalise(s1,s2)
    in
	(cons(z, fn () => first_st(lex(force ns1, force ns2,1))), 
	 cons(t, fn () => second_st(lex(force ns1, force ns2,1))))
    end;

(*************************************** THIS WIDE *******************************)

fun set_n_one([],_) = raise BUG
  | set_n_one (a::l,0) = 1::l
  | set_n_one (a::l, n) = a::set_n_one (l, n-1)
    
fun int_gr 1 = ([1],1)
  | int_gr n = 
    let val (list, exp) = int_gr (n-1) in
	(set_n_one(flip(([0]@list@[0,0]), (exp+1)),exp),(exp+1))
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

fun negate_int 0 = [0,1,1]
  | negate_int n = 
    let
	val (ans,exp) = int_gr n
    in
	if (exp mod 2 = 0) then (comp_fin_list([(exp div 2)+1,1,1]@ans))
	else (comp_fin_list([(exp div 2)+2,1,1,0]@ans))
    end

fun digit_gr 0 = put([0,1,1])
  | digit_gr n  = 
    if (n>0) then
	let val (ans,exp) = int_gr n in
	    if (exp mod 2 = 0) then put([(exp div 2)+1,1,1]@ans)
	    else put([(exp div 2)+2,1,1,0]@ans)
	end
    else
	put(negate_int (abs(n)))
	
(*************************************** THIS WIDE *******************************)

(* Conversion from decimal to GR *)
fun post_d d 0 = []
  | post_d d n =
	let
	    val x = 10.0 * d
	in
	    (floor x::(post_d (x-real(floor x)) (n-1)))
	end;

fun pre_d 0 = []
  | pre_d d = ((pre_d(d div 10))@[(d mod 10)]);

fun pre_gr[] = digit_gr 0
  | pre_gr[a] = digit_gr a
  | pre_gr(a::list) = addition(digit_gr a, mult(digit_gr 10, pre_gr(list)));

fun post_gr [] = digit_gr 0
| post_gr(a::list) = divide(addition(digit_gr a, post_gr(list)), digit_gr 10);

fun list_to_gr (list1,list2) = addition(post_gr(list2),pre_gr(rev(list1)));

fun dec_gr d n =
    let
	val x = d
    in
    if (x<0.0) then
	simplify(comp(list_to_gr(pre_d (floor(~x)), post_d ((~x)-real(floor(~x))) n)))
    else
	simplify(list_to_gr(pre_d (floor(x)), post_d (x-real(floor(x))) n))
    end;

(*********************************************************************************)
(* Conversion from GR to decimal *)

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

fun gr_decimal'([], _)= 0.0
  | gr_decimal'((x::list), n) = (real(x)*n)+gr_decimal'(list, n*gr);
fun gr_decimal(list) = gr_decimal'(rev(list),1.0);

fun bot x = if ((x<0.5) andalso (x>(~0.5))) then 0
	    else floor x;

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
fun flip_first_simp (cons(0, s), n)=
    let 
	val working_list = take n (force s)
	val (sign::list) = flip([0]@(working_list)@[0,0], 2) in 
	if (sign=1) then (* sign=1 => value of list is positive *)
	    (working_list, 1)
	else (* sign=0 => value of list is negative *)
	    let val (1::negate_list) = take (n+3) (comp(cons(0,s)))
		val (overflow::one::zero::x::y::rest) = flip([0]@negate_list@[0,0], 3)
	    in
		if ((overflow=1) andalso (x=0) andalso (y=0)) then
		    (1::1::rest,~1)
		else
		    (x::y::rest, ~1)
	    end
    end;

fun first 0 _ = []
| first n (a::list) = a::(first (n-1) list);

fun simp(z::1::0::list) = if (z>0) then simp((z-1)::list)
			  else (z::1::0::list)
  | simp(list) = (list);
    
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
    end;

fun conv_to_d(stream,digits) =
    let
	val take_digits = 5*digits+4
	val (s2,exp) = make_exp_0(stream)
	val (gr_list,sign) = flip_first_simp (s2, take_digits)
	val (list_of_digits,n) = eval(0::gr_list, digits)
    in
	(rev(list_of_digits), exp, sign, n)
    end;

(************************************************************)
(* Conversion from a finite GR list to binary *)
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

fun cut_end'([0], h::list) = cut_end'([h],list)
  | cut_end'([1], list) = rev(list)@[1]
  | cut_end'((h::list),list2) = cut_end'(list,h::list2)
  | cut_end' _  = raise BUG;

fun cut_end(list) = cut_end'(list,[]);

fun con_bin'([], 1) = 1
  | con_bin'(0::list, n) = 2*con_bin'(list, n*2)
  | con_bin'(1::list, n) = 2*con_bin'(list, n*2)
  | con_bin' _ = raise BUG;

fun bin(_,0) = []
  | bin (list, d) = 
    let
	val list_0s = list@[0,0,0,0]
	val two_lex_list = add_l(list_0s,list_0s,0,0)
	val fliped_two_list = flip([0]@two_lex_list,4)
	val (0::a::b::c::new_list) = cut_end(fliped_two_list)
    in
	if (b = 1) then
	    1::bin(c::new_list, d-1)
	else if (a = 1) then
	    1::bin(1::new_list, d-1)
	else (*inter = GREATER *)
	    0::bin(c::new_list, d-1)
    end;	    

fun bin_dec ([]) = 0.5
| bin_dec (0::l) = bin_dec(l)/2.0
| bin_dec (1::l) = (bin_dec(l)+1.0)/2.0
| bin_dec _ = raise BUG;

(* Only case where s>0 *)
(*fun convert (s,n,d) = 
    let 
	val (s1,exp) = make_exp_0(s)
	val (cons(0,str),sign) = flip_first_simp(s1,n)
	val list = take (2*n) (force str)
	in
	real(sign)*(bin_dec(bin (list, d))*power(10.0,exp))
    end;
*)
(****************************************************************)

