include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "wa.mm"
include "wtru.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "elpwi.mm"
include "syl.mm"
include "sstr.mm"
include "ancoms.mm"
include "syl2an.mm"
include "elpwgded.mm"
include "uun0.1.mm"
include "ex.mm"
include "alrimiv.mm"
include "dfss2.mm"
include "biimpri.mm"
include "iin1.mm"

theorem sspwimp
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
    @4
    cvv
    wcel
    #
    @0
    @5
    wa
    #
    @4
    cB
    wss
    #
    @6
    @9
    wtru
    vx
    vex
    a1i
    #
    @0
    @0
    @4
    cA
    wss
    #
    @11
    @5
    @0
    id
    @5
    @5
    @13
    @5
    id
    @4
    cA
    elpwi
    syl
    @13
    @0
    @11
    @4
    cA
    cB
    sstr
    ancoms
    syl2an
    #
    wtru
    @10
    @4
    cB
    @12
    @14
    elpwgded
    uun0.1
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
    iin1
end
