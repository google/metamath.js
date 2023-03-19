
axiom df-fin2
  let vx: setvar x
  let vy: setvar y
  assert |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\ [C.] Or y ) -> U. y e. y ) }
end
