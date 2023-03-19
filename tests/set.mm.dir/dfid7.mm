include "cid.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "wss.mm"
include "wtru.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "dfid4.mm"
include "ancom.mm"
include "truan.mm"
include "bitri.mm"
include "abbii.mm"
include "inteqi.mm"
include "vex.mm"
include "intmin2.mm"
include "eqtri.mm"
include "mpteq2i.mm"
include "eqtr4i.mm"

theorem dfid7
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- _I = ( x e. _V |-> |^| { y | ( x C_ y /\ T. ) } )

  proof
    cid
    vx
    cvv
    vx
    cv
    #
    cmpt
    vx
    cvv
    @0
    vy
    cv
    wss
    #
    wtru
    wa
    #
    vy
    cab
    #
    cint
    #
    cmpt
    vx
    dfid4
    vx
    cvv
    @4
    @0
    @4
    @1
    vy
    cab
    #
    cint
    @0
    @3
    @5
    @2
    @1
    vy
    @2
    wtru
    @1
    wa
    @1
    @1
    wtru
    ancom
    @1
    truan
    bitri
    abbii
    inteqi
    vy
    @0
    vx
    vex
    intmin2
    eqtri
    mpteq2i
    eqtr4i
end
