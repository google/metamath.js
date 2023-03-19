
axiom df-ovol
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- vol* = ( x e. ~P RR |-> inf ( { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( x C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) } , RR* , < ) )
end
