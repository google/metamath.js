
axiom df-carsg
  let ve: setvar e
  let vm: setvar m
  let va: setvar a
  assert |- toCaraSiga = ( m e. _V |-> { a e. ~P U. dom m | A. e e. ~P U. dom m ( ( m ` ( e i^i a ) ) +e ( m ` ( e \ a ) ) ) = ( m ` e ) } )
end
