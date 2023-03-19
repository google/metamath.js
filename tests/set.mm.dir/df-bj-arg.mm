
axiom df-bj-arg
  let vx: setvar x
  assert |- Arg = ( x e. ( CCbar \ { 0 } ) |-> if ( x e. CC , ( Im ` ( log ` x ) ) , ( 1st ` x ) ) )
end
