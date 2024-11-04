(* see report section 2.4 *)

fun forever' ([],list) = forever' (list, list)
| forever' (x::list1, list) = cons(x, fn()=> forever' (list1,list));
				   
fun forever list = forever' (list, list);

fun kleene ([], loop) = forever(loop)
| kleene (x::prefix, loop) = cons(x, fn()=> kleene(prefix, loop));

val half = gr_to_dec (take 30 (kleene([0],[1,0,0])));

val qrtr = gr_to_dec (take 30 (kleene([0,0],[1,0,0,0,0,0])));

val ehth = gr_to_dec (take 30 (kleene([0,0,0,0],[1,0,1,0,0,0,0,0,0,0,0,0])));

val sxtnth = (gr_to_dec (take 40 (kleene([0,0,0,0],[0,0,1,1,0,0,1,0,0,1,0,0,1,0,0,1,1,1,0,0,0,0,0,0,0,0,0]))))*16.0;

fun half([]) = []
| half (2::list) = 1::half(list)
| half (0::list) = 0::half(list)
| half (x::list) = x::half(list);

fun zero_two([])=[]
| zero_two([1])=[3]
| zero_two([1,1])=[4]
| zero_two([1,2])=[5]
| zero_two(0::list)=0::zero_two(list)
| zero_two(1::0::0::list)=0::zero_two(1::1::list)
| zero_two(1::0::1::list)=0::zero_two(1::2::list)
| zero_two(1::1::0::list)=0::2::zero_two(1::list)
| zero_two(1::1::1::list)=2::0::0::zero_two(list)
| zero_two(1::2::0::0::list)=2::0::0::zero_two(1::list)
| zero_two(1::2::0::1::list)=2::0::0::2::zero_two(list)
| zero_two(1::2::1::list)=2::zero_two(1::0::list)
| zero_two(list) = zero_two(list@[0]);


fun div_two(list) = half(zero_two(list));

fun l [] = 0
| l (x::list) = 1+(l list);

fun d_t(list) = let val ans = half(zero_two(list))
val length = l ans in
remove (length-1) ans
end;

val half = [0,1,1,0,1,1];
val qrtr = div_two(half@half);
val ehth =div_two(qrtr@qrtr);
val sxtnth = div_two(ehth@ehth);
val thrtyto= div_two(sxtnth@sxtnth);
val fadyfaw = div_two(thrtyto@thrtyto);
