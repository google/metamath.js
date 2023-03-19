
axiom df-cnfn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  assert |- ContFn = { t e. ( CC ^m ~H ) | A. x e. ~H A. y e. RR+ E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z -> ( abs ` ( ( t ` w ) - ( t ` x ) ) ) < y ) }
end
