include "csuc.mm"
include "cconn.mm"
include "wcel.mm"
include "ctop.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "cpr.mm"
include "wss.mm"
include "con0.mm"
include "onsuctop.mm"
include "ax-mp.mm"
include "cv.mm"
include "wa.mm"
include "elin.mm"
include "wceq.mm"
include "wo.mm"
include "cdif.mm"
include "elsuci.mm"
include "cuni.mm"
include "onunisuci.mm"
include "eqcomi.mm"
include "cldopn.mm"
include "wi.mm"
include "onsuci.mm"
include "oneli.mm"
include "wn.mm"
include "elndif.mm"
include "wne.mm"
include "on0eln0.mm"
include "biimprd.mm"
include "necon1bd.mm"
include "ssdif0.mm"
include "onssneli.mm"
include "sylbir.mm"
include "syl56.mm"
include "con2d.mm"
include "syl.mm"
include "sylcom.mm"
include "orim1d.mm"
include "impcom.mm"
include "vex.mm"
include "elpr.mm"
include "sylibr.mm"
include "syl2an.mm"
include "sylbi.mm"
include "ssriv.mm"
include "isconn2.mm"
include "mpbir2an.mm"

theorem onsucconni
  let cA: class A
  let vx: setvar x
  assume onsucconni.1: |- A e. On


  assert |- suc A e. Conn

  proof
    cA
    csuc
    #
    cconn
    wcel
    @0
    ctop
    wcel
    #
    @0
    @0
    ccld
    cfv
    #
    cin
    #
    c0
    cA
    cpr
    #
    wss
    cA
    con0
    wcel
    @1
    onsucconni.1
    cA
    onsuctop
    ax-mp
    vx
    @3
    @4
    vx
    cv
    #
    @3
    wcel
    @5
    @0
    wcel
    #
    @5
    @2
    wcel
    #
    wa
    @5
    @4
    wcel
    #
    @5
    @0
    @2
    elin
    @6
    @5
    cA
    wcel
    #
    @5
    cA
    wceq
    #
    wo
    #
    cA
    @5
    cdif
    #
    @0
    wcel
    #
    @8
    @7
    @5
    cA
    elsuci
    @5
    @0
    cA
    @0
    cuni
    cA
    cA
    onsucconni.1
    onunisuci
    eqcomi
    #
    cldopn
    @11
    @13
    wa
    @5
    c0
    wceq
    #
    @10
    wo
    #
    @8
    @13
    @11
    @16
    @13
    @9
    @15
    @10
    @13
    @12
    con0
    wcel
    #
    @9
    @15
    wi
    @0
    @12
    cA
    onsucconni.1
    onsuci
    oneli
    @17
    @9
    c0
    @5
    wcel
    #
    wn
    @15
    @17
    @18
    @9
    @18
    c0
    @12
    wcel
    #
    wn
    @17
    @12
    c0
    wceq
    #
    @9
    wn
    #
    c0
    @5
    cA
    elndif
    @17
    @19
    @12
    c0
    @17
    @19
    @12
    c0
    wne
    @12
    on0eln0
    biimprd
    necon1bd
    @20
    cA
    @5
    wss
    @21
    cA
    @5
    ssdif0
    cA
    @5
    onsucconni.1
    onssneli
    sylbir
    syl56
    con2d
    @9
    @18
    @5
    c0
    @9
    @5
    con0
    wcel
    #
    @5
    c0
    wne
    #
    @18
    wi
    cA
    @5
    onsucconni.1
    oneli
    @22
    @18
    @23
    @5
    on0eln0
    biimprd
    syl
    necon1bd
    sylcom
    syl
    orim1d
    impcom
    @5
    c0
    cA
    vx
    vex
    elpr
    sylibr
    syl2an
    sylbi
    ssriv
    @0
    cA
    @14
    isconn2
    mpbir2an
end
