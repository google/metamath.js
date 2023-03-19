
axiom df-finxp
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let vn: setvar n
  let cN: class N
  assert |- ( U ^^ N ) = { y | ( N e. _om /\ (/) = ( rec ( ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) , <. N , y >. ) ` N ) ) }
end
