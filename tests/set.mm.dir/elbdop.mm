include "cv.mm"
include "cnop.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "clo.mm"
include "cbo.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "df-bdop.mm"
include "elrab2.mm"

theorem elbdop
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp <-> ( T e. LinOp /\ ( normop ` T ) < +oo ) )

  proof
    vt
    cv
    #
    cnop
    cfv
    #
    cpnf
    clt
    wbr
    cT
    cnop
    cfv
    #
    cpnf
    clt
    wbr
    vt
    cT
    clo
    cbo
    @0
    cT
    wceq
    @1
    @2
    cpnf
    clt
    @0
    cT
    cnop
    fveq2
    breq1d
    vt
    df-bdop
    elrab2
end
