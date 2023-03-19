include "cbo.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "chil.mm"
include "wf.mm"
include "bdopf.mm"
include "nmopgtmnf.mm"
include "syl.mm"
include "clo.mm"
include "elbdop.mm"
include "simprbi.mm"
include "cxr.mm"
include "wa.mm"
include "wb.mm"
include "nmopxr.mm"
include "xrrebnd.mm"
include "3syl.mm"
include "mpbir2and.mm"

theorem nmopre
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp -> ( normop ` T ) e. RR )

  proof
    cT
    cbo
    wcel
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    cmnf
    @1
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    @0
    chil
    chil
    cT
    wf
    #
    @3
    cT
    bdopf
    #
    cT
    nmopgtmnf
    syl
    @0
    cT
    clo
    wcel
    @4
    cT
    elbdop
    simprbi
    @0
    @5
    @1
    cxr
    wcel
    @2
    @3
    @4
    wa
    wb
    @6
    cT
    nmopxr
    @1
    xrrebnd
    3syl
    mpbir2and
end
