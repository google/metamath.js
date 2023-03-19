
axiom df-plr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assert |- +R = { <. <. x , y >. , z >. | ( ( x e. R. /\ y e. R. ) /\ E. w E. v E. u E. f ( ( x = [ <. w , v >. ] ~R /\ y = [ <. u , f >. ] ~R ) /\ z = [ <. ( w +P. u ) , ( v +P. f ) >. ] ~R ) ) }
end
