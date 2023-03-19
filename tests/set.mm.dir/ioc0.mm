include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "crab.mm"
include "iocval.mm"
include "eqeq1d.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "df-ne.mm"
include "rabn0.mm"
include "bitr3i.mm"
include "wi.mm"
include "xrltletr.mm"
include "3com23.mm"
include "3expa.mm"
include "rexlimdva.mm"
include "w3a.mm"
include "cq.mm"
include "qbtwnxr.mm"
include "qre.mm"
include "rexrd.mm"
include "a1i.mm"
include "xrltle.mm"
include "3ad2antr2.mm"
include "anim2d.mm"
include "anim12d.mm"
include "ex.mm"
include "syl.mm"
include "adantr.mm"
include "pm2.43b.mm"
include "reximdv2.mm"
include "mpd.mm"
include "3expia.mm"
include "impbid.mm"
include "syl5bb.mm"
include "xrltnle.mm"
include "bitrd.mm"
include "con4bid.mm"

theorem ioc0
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( ( A (,] B ) = (/) <-> B <_ A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cioc
    co
    #
    c0
    wceq
    cA
    vx
    cv
    #
    clt
    wbr
    #
    @4
    cB
    cle
    wbr
    #
    wa
    #
    vx
    cxr
    crab
    #
    c0
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    @2
    @3
    @8
    c0
    vx
    cA
    cB
    iocval
    eqeq1d
    @2
    @9
    @10
    @2
    @9
    wn
    #
    cA
    cB
    clt
    wbr
    #
    @10
    wn
    @11
    @7
    vx
    cxr
    wrex
    #
    @2
    @12
    @11
    @8
    c0
    wne
    @13
    @8
    c0
    df-ne
    @7
    vx
    cxr
    rabn0
    bitr3i
    @2
    @13
    @12
    @2
    @7
    @12
    vx
    cxr
    @0
    @1
    @4
    cxr
    wcel
    #
    @7
    @12
    wi
    #
    @0
    @14
    @1
    @15
    cA
    @4
    cB
    xrltletr
    3com23
    3expa
    rexlimdva
    @0
    @1
    @12
    @13
    @0
    @1
    @12
    w3a
    #
    @5
    @4
    cB
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    @13
    vx
    cA
    cB
    qbtwnxr
    @16
    @18
    @7
    vx
    cq
    cxr
    @16
    @4
    cq
    wcel
    #
    @18
    wa
    #
    @14
    @7
    wa
    #
    @19
    @16
    @20
    @21
    wi
    #
    wi
    #
    @18
    @19
    @14
    @23
    @19
    @4
    @4
    qre
    rexrd
    #
    @14
    @16
    @22
    @14
    @16
    wa
    #
    @19
    @14
    @18
    @7
    @19
    @14
    wi
    @25
    @24
    a1i
    @25
    @17
    @6
    @5
    @14
    @0
    @1
    @17
    @6
    wi
    @12
    @4
    cB
    xrltle
    3ad2antr2
    anim2d
    anim12d
    ex
    syl
    adantr
    pm2.43b
    reximdv2
    mpd
    3expia
    impbid
    syl5bb
    cA
    cB
    xrltnle
    bitrd
    con4bid
    bitrd
end
