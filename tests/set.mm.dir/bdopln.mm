include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "elbdop.mm"
include "simplbi.mm"

theorem bdopln
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp -> T e. LinOp )

  proof
    cT
    cbo
    wcel
    cT
    clo
    wcel
    cT
    cnop
    cfv
    cpnf
    clt
    wbr
    cT
    elbdop
    simplbi
end
