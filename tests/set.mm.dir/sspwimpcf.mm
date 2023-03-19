include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "vex.mm"
include "id.mm"
include "elpwi.mm"
include "syl.mm"
include "sstr2.mm"
include "impcom.mm"
include "syl2an.mm"
include "elpwg.mm"
include "biimpar.mm"
include "eel021old.mm"
include "ex.mm"
include "alrimiv.mm"
include "dfss2.mm"
include "biimpri.mm"
include "iin1.mm"

theorem sspwimpcf
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
    @4
    cB
    wss
    #
    @6
    vx
    vex
    @0
    @0
    @4
    cA
    wss
    #
    @10
    @5
    @0
    id
    @5
    @5
    @11
    @5
    id
    @4
    cA
    elpwi
    syl
    @11
    @0
    @10
    @4
    cA
    cB
    sstr2
    impcom
    syl2an
    @9
    @6
    @10
    @4
    cB
    cvv
    elpwg
    biimpar
    eel021old
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
