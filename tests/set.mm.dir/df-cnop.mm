
axiom df-cnop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  assert |- ContOp = { t e. ( ~H ^m ~H ) | A. x e. ~H A. y e. RR+ E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z -> ( normh ` ( ( t ` w ) -h ( t ` x ) ) ) < y ) }
end
