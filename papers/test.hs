

epsilon p = (x0,x1,x2)
 where y   = p(True,True,p(True,True,True))
       x0  = p(True,y,p(True,y,True))
       x1  = p(x0,True,p(x0,True,True))
       x2  = p(x0,x1,True)

forsome p = p(epsilon p)
forevery p = not(forsome(not.p))

True --> p = p
False --> p = True

q(a,b,c) = (a --> (b --> c)) --> ((a && b) --> c)
r(a,b,c) = ((a --> c) && (b --> c)) --> ((a || b) --> c)
