
axiom df-fib
  let vw: setvar w
  assert |- Fibci = ( <" 0 1 "> seqstr ( w e. ( Word NN0 i^i ( `' # " ( ZZ>= ` 2 ) ) ) |-> ( ( w ` ( ( # ` w ) - 2 ) ) + ( w ` ( ( # ` w ) - 1 ) ) ) ) )
end
