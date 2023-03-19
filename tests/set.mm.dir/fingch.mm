include "cfn.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "wa.mm"
include "wn.mm"
include "wal.mm"
include "cab.mm"
include "cun.mm"
include "cgch.mm"
include "ssun1.mm"
include "df-gch.mm"
include "sseqtr4i.mm"

theorem fingch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- Fin C_ GCH

  proof
    cfn
    cfn
    vx
    cv
    #
    vy
    cv
    #
    csdm
    wbr
    @1
    @0
    cpw
    csdm
    wbr
    wa
    wn
    vy
    wal
    vx
    cab
    #
    cun
    cgch
    cfn
    @2
    ssun1
    vx
    vy
    df-gch
    sseqtr4i
end
