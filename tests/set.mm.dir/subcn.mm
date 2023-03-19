include "cmin.mm"
include "subf.mm"
include "cv.mm"
include "subcn2.mm"
include "addcnlem.mm"

theorem subcn
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


  assert |- - e. ( ( J tX J ) Cn J )

  proof
    vy
    vz
    vv
    vu
    cmin
    cJ
    va
    vb
    vc
    addcn.j
    subf
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
    subcn2
    addcnlem
end
