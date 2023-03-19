
axiom df-xrh
  let vx: setvar x
  let vr: setvar r
  assert |- RR*Hom = ( r e. _V |-> ( x e. RR* |-> if ( x e. RR , ( ( RRHom ` r ) ` x ) , if ( x = +oo , ( ( lub ` r ) ` ( ( RRHom ` r ) " RR ) ) , ( ( glb ` r ) ` ( ( RRHom ` r ) " RR ) ) ) ) ) )
end
