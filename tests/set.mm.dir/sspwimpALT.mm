include "wss.mm"
include "cpw.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "wa.mm"
include "wtru.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "elpwi.mm"
include "syl.mm"
include "sylan9ssr.mm"
include "elpwgded.mm"
include "uunT1.mm"
include "ex.mm"
include "alrimiv.mm"
include "dfss2.mm"
include "biimpri.mm"
include "idiALT.mm"

theorem sspwimpALT
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B -> ~P A C_ ~P B )

  proof
    cA
    cB
    wss
    #
    cA
    cpw
    #
    cB
    cpw
    #
    wss
    #
    wi
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    wi
    #
    vx
    wal
    #
    @3
    @0
    @7
    vx
    @0
    @5
    @6
    @0
    @5
    wa
    #
    @6
    wtru
    @9
    @4
    cB
    @4
    cvv
    wcel
    wtru
    vx
    vex
    a1i
    @5
    @0
    @4
    cA
    cB
    @5
    @5
    @4
    cA
    wss
    @5
    id
    @4
    cA
    elpwi
    syl
    @0
    id
    sylan9ssr
    elpwgded
    uunT1
    ex
    alrimiv
    @3
    @8
    vx
    @1
    @2
    dfss2
    biimpri
    syl
    idiALT
end
