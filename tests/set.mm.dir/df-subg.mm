
axiom df-subg
  let vw: setvar w
  let vs: setvar s
  assert |- SubGrp = ( w e. Grp |-> { s e. ~P ( Base ` w ) | ( w |`s s ) e. Grp } )
end
