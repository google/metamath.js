
axiom df-rngiso
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- RingIso = ( r e. _V , s e. _V |-> { f e. ( r RingHom s ) | `' f e. ( s RingHom r ) } )
end
