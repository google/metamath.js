
axiom df-ltxr
  let vx: setvar x
  let vy: setvar y
  assert |- < = ( { <. x , y >. | ( x e. RR /\ y e. RR /\ x <RR y ) } u. ( ( ( RR u. { -oo } ) X. { +oo } ) u. ( { -oo } X. RR ) ) )
end
