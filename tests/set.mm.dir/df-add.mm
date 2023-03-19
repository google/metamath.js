
axiom df-add
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assert |- + = { <. <. x , y >. , z >. | ( ( x e. CC /\ y e. CC ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = <. ( w +R u ) , ( v +R f ) >. ) ) }
end
