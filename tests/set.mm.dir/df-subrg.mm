
axiom df-subrg
  let vw: setvar w
  let vs: setvar s
  assert |- SubRing = ( w e. Ring |-> { s e. ~P ( Base ` w ) | ( ( w |`s s ) e. Ring /\ ( 1r ` w ) e. s ) } )
end
