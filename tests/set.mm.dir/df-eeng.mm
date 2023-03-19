
axiom df-eeng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vn: setvar n
  assert |- EEG = ( n e. NN |-> ( { <. ( Base ` ndx ) , ( EE ` n ) >. , <. ( dist ` ndx ) , ( x e. ( EE ` n ) , y e. ( EE ` n ) |-> sum_ i e. ( 1 ... n ) ( ( ( x ` i ) - ( y ` i ) ) ^ 2 ) ) >. } u. { <. ( Itv ` ndx ) , ( x e. ( EE ` n ) , y e. ( EE ` n ) |-> { z e. ( EE ` n ) | z Btwn <. x , y >. } ) >. , <. ( LineG ` ndx ) , ( x e. ( EE ` n ) , y e. ( ( EE ` n ) \ { x } ) |-> { z e. ( EE ` n ) | ( z Btwn <. x , y >. \/ x Btwn <. z , y >. \/ y Btwn <. x , z >. ) } ) >. } ) )
end
