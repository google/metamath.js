include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wrex.mm"
include "cpw.mm"
include "ciun.mm"
include "wss.mm"
include "wcel.mm"
include "sseq2.mm"
include "biimprcd.mm"
include "reximdv.mm"
include "com12.mm"
include "ssiun.mm"
include "uniiun.mm"
include "syl6sseqr.mm"
include "impbid1.mm"
include "selpw.mm"
include "eliun.mm"
include "rexbii.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "ssid.mm"
include "uniex.mm"
include "elpw.mm"
include "eleq2.mm"
include "syl5bbr.mm"
include "mpbii.mm"
include "sylib.mm"
include "wa.mm"
include "elssuni.mm"
include "elpwi.mm"
include "anim12i.mm"
include "eqss.mm"
include "sylibr.mm"
include "ex.mm"
include "reximia.mm"
include "syl.mm"
include "impbii.mm"

theorem iunpw
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume iunpw.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( E. x e. A x = U. A <-> ~P U. A = U_ x e. A ~P x )

  proof
    vx
    cv
    #
    cA
    cuni
    #
    wceq
    #
    vx
    cA
    wrex
    #
    @1
    cpw
    #
    vx
    cA
    @0
    cpw
    #
    ciun
    #
    wceq
    #
    @3
    vy
    @4
    @6
    @3
    vy
    cv
    #
    @1
    wss
    #
    @8
    @0
    wss
    #
    vx
    cA
    wrex
    #
    @8
    @4
    wcel
    @8
    @6
    wcel
    #
    @3
    @9
    @11
    @9
    @3
    @11
    @9
    @2
    @10
    vx
    cA
    @2
    @10
    @9
    @0
    @1
    @8
    sseq2
    biimprcd
    reximdv
    com12
    @11
    @8
    vx
    cA
    @0
    ciun
    @1
    vx
    cA
    @0
    @8
    ssiun
    vx
    cA
    uniiun
    syl6sseqr
    impbid1
    vy
    @1
    selpw
    @12
    @8
    @5
    wcel
    #
    vx
    cA
    wrex
    @11
    vx
    @8
    cA
    @5
    eliun
    @13
    @10
    vx
    cA
    vy
    @0
    selpw
    rexbii
    bitri
    3bitr4g
    eqrdv
    @7
    @1
    @5
    wcel
    #
    vx
    cA
    wrex
    #
    @3
    @7
    @1
    @6
    wcel
    #
    @15
    @7
    @1
    @1
    wss
    #
    @16
    @1
    ssid
    @17
    @1
    @4
    wcel
    @7
    @16
    @1
    @1
    cA
    iunpw.1
    uniex
    elpw
    @4
    @6
    @1
    eleq2
    syl5bbr
    mpbii
    vx
    @1
    cA
    @5
    eliun
    sylib
    @14
    @2
    vx
    cA
    @0
    cA
    wcel
    #
    @14
    @2
    @18
    @14
    wa
    @0
    @1
    wss
    #
    @1
    @0
    wss
    #
    wa
    @2
    @18
    @19
    @14
    @20
    @0
    cA
    elssuni
    @1
    @0
    elpwi
    anim12i
    @0
    @1
    eqss
    sylibr
    ex
    reximia
    syl
    impbii
end
