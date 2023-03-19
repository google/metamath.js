include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "cioc.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "iccid.mm"
include "3ad2ant1.mm"
include "uneq1d.mm"
include "simp1.mm"
include "simp2.mm"
include "xrleid.mm"
include "simp3.mm"
include "clt.mm"
include "df-icc.mm"
include "df-ioc.mm"
include "cv.mm"
include "xrltnle.mm"
include "xrletr.mm"
include "wa.mm"
include "simprr.mm"
include "wi.mm"
include "simpl1.mm"
include "simpl3.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "ex.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "eqtr3d.mm"

theorem snunioc
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> ( { A } u. ( A (,] B ) ) = ( A [,] B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cA
    cicc
    co
    #
    cA
    cB
    cioc
    co
    #
    cun
    #
    cA
    csn
    #
    @5
    cun
    cA
    cB
    cicc
    co
    #
    @3
    @4
    @7
    @5
    @0
    @1
    @4
    @7
    wceq
    @2
    cA
    iccid
    3ad2ant1
    uneq1d
    @3
    @0
    @0
    @1
    cA
    cA
    cle
    wbr
    #
    @2
    @6
    @8
    wceq
    @0
    @1
    @2
    simp1
    #
    @10
    @0
    @1
    @2
    simp2
    @0
    @1
    @9
    @2
    cA
    xrleid
    3ad2ant1
    @0
    @1
    @2
    simp3
    vx
    vy
    vz
    vw
    cA
    cA
    cB
    cioc
    cicc
    cle
    cle
    clt
    cle
    cicc
    cle
    cle
    vx
    vy
    vz
    df-icc
    #
    vx
    vy
    vz
    df-ioc
    cA
    vw
    cv
    #
    xrltnle
    @11
    @12
    cA
    cB
    xrletr
    @0
    @0
    @12
    cxr
    wcel
    #
    w3a
    #
    @9
    cA
    @12
    clt
    wbr
    #
    wa
    #
    cA
    @12
    cle
    wbr
    #
    @14
    @16
    wa
    #
    @15
    @17
    @14
    @9
    @15
    simprr
    @18
    @0
    @13
    @15
    @17
    wi
    @0
    @0
    @13
    @16
    simpl1
    @0
    @0
    @13
    @16
    simpl3
    cA
    @12
    xrltle
    syl2anc
    mpd
    ex
    ixxun
    syl32anc
    eqtr3d
end
