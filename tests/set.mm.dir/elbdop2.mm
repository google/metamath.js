include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "elbdop.mm"
include "chil.mm"
include "wf.mm"
include "wb.mm"
include "lnopf.mm"
include "nmopreltpnf.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem elbdop2
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp <-> ( T e. LinOp /\ ( normop ` T ) e. RR ) )

  proof
    cT
    cbo
    wcel
    cT
    clo
    wcel
    #
    cT
    cnop
    cfv
    #
    cpnf
    clt
    wbr
    #
    wa
    @0
    @1
    cr
    wcel
    #
    wa
    cT
    elbdop
    @0
    @3
    @2
    @0
    chil
    chil
    cT
    wf
    @3
    @2
    wb
    cT
    lnopf
    cT
    nmopreltpnf
    syl
    pm5.32i
    bitr4i
end
