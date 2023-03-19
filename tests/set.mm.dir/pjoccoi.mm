include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "ccom.mm"
include "ch0o.mm"
include "wceq.mm"
include "chssii.mm"
include "ococss.mm"
include "choccli.mm"
include "pjorthcoi.mm"
include "mp2b.mm"

theorem pjoccoi
  let cH: class H
  let vx: setvar x
  assume pjidmco.1: |- H e. CH


  assert |- ( ( projh ` H ) o. ( projh ` ( _|_ ` H ) ) ) = 0hop

  proof
    cH
    chil
    wss
    cH
    cH
    cort
    cfv
    #
    cort
    cfv
    wss
    cH
    cpjh
    cfv
    @0
    cpjh
    cfv
    ccom
    ch0o
    wceq
    cH
    pjidmco.1
    chssii
    cH
    ococss
    cH
    @0
    pjidmco.1
    cH
    pjidmco.1
    choccli
    pjorthcoi
    mp2b
end
