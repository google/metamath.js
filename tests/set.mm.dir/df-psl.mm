
axiom df-psl
  let vx: setvar x
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- polySplitLim = ( r e. _V , p e. ( ( ~P ( Base ` r ) i^i Fin ) ^m NN ) |-> [_ ( 1st o. seq 0 ( ( g e. _V , q e. _V |-> [_ ( 1st ` g ) / e ]_ [_ ( 1st ` e ) / s ]_ [_ ( s splitFld ran ( x e. q |-> ( x o. ( 2nd ` g ) ) ) ) / f ]_ <. f , ( ( 2nd ` g ) o. ( 2nd ` f ) ) >. ) , ( p u. { <. 0 , <. <. r , (/) >. , ( _I |` ( Base ` r ) ) >. >. } ) ) ) / f ]_ ( ( 1st o. ( f shift 1 ) ) HomLim ( 2nd o. f ) ) )
end
