include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "cvv.mm"
include "wcel.mm"
include "pwex.mm"
include "cv.mm"
include "csn.mm"
include "snelpwi.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "vex.mm"
include "sneqr.mm"
include "sneq.mm"
include "impbii.mm"
include "a1i.mm"
include "dom3.mm"
include "mp2an.mm"
include "wf1o.mm"
include "wex.mm"
include "wfo.mm"
include "canth.mm"
include "f1ofo.mm"
include "mto.mm"
include "nex.mm"
include "bren.mm"
include "mtbir.mm"
include "brsdom.mm"
include "mpbir2an.mm"

theorem canth2
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume canth2.1: |- A e. _V


  assert |- A ~< ~P A

  proof
    cA
    cA
    cpw
    #
    csdm
    wbr
    cA
    @0
    cdom
    wbr
    #
    cA
    @0
    cen
    wbr
    #
    wn
    cA
    cvv
    wcel
    @0
    cvv
    wcel
    @1
    canth2.1
    cA
    canth2.1
    pwex
    vx
    vy
    cA
    @0
    vx
    cv
    #
    csn
    #
    vy
    cv
    #
    csn
    #
    cvv
    cvv
    @3
    cA
    snelpwi
    @4
    @6
    wceq
    #
    @3
    @5
    wceq
    #
    wb
    @3
    cA
    wcel
    @5
    cA
    wcel
    wa
    @7
    @8
    @3
    @5
    vx
    vex
    sneqr
    @3
    @5
    sneq
    impbii
    a1i
    dom3
    mp2an
    @2
    cA
    @0
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @10
    vf
    @10
    cA
    @0
    @9
    wfo
    cA
    @9
    canth2.1
    canth
    cA
    @0
    @9
    f1ofo
    mto
    nex
    cA
    @0
    vf
    bren
    mtbir
    cA
    @0
    brsdom
    mpbir2an
end
