
axiom df-mul
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assert |- x. = { <. <. x , y >. , z >. | ( ( x e. CC /\ y e. CC ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = <. ( ( w .R u ) +R ( -1R .R ( v .R f ) ) ) , ( ( v .R u ) +R ( w .R f ) ) >. ) ) }
end
