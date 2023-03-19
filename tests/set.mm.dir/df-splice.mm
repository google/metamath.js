
axiom df-splice
  let vs: setvar s
  let vb: setvar b
  assert |- splice = ( s e. _V , b e. _V |-> ( ( ( s substr <. 0 , ( 1st ` ( 1st ` b ) ) >. ) ++ ( 2nd ` b ) ) ++ ( s substr <. ( 2nd ` ( 1st ` b ) ) , ( # ` s ) >. ) ) )
end
