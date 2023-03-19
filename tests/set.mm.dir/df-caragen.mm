
axiom df-caragen
  let ve: setvar e
  let vo: setvar o
  let va: setvar a
  assert |- CaraGen = ( o e. OutMeas |-> { e e. ~P U. dom o | A. a e. ~P U. dom o ( ( o ` ( a i^i e ) ) +e ( o ` ( a \ e ) ) ) = ( o ` a ) } )
end
