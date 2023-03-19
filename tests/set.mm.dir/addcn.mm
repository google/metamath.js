include "caddc.mm"
include "ax-addf.mm"
include "cv.mm"
include "addcn2.mm"
include "addcnlem.mm"

theorem addcn
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let c.pl: class .+
  assume addcn.j: |- J = ( TopOpen ` CCfld )


  assert |- + e. ( ( J tX J ) Cn J )

  proof
    vy
    vz
    vv
    vu
    caddc
    cJ
    va
    vb
    vc
    addcn.j
    ax-addf
    vy
    vz
    vv
    vu
    va
    cv
    vb
    cv
    vc
    cv
    addcn2
    addcnlem
end
