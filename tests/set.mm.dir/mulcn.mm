include "cmul.mm"
include "ax-mulf.mm"
include "cv.mm"
include "mulcn2.mm"
include "addcnlem.mm"

theorem mulcn
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


  assert |- x. e. ( ( J tX J ) Cn J )

  proof
    vy
    vz
    vv
    vu
    cmul
    cJ
    va
    vb
    vc
    addcn.j
    ax-mulf
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
    mulcn2
    addcnlem
end
