include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cioo.mm"
include "co.mm"
include "cicc.mm"
include "cun.mm"
include "csn.mm"
include "cico.mm"
include "uncom.mm"
include "wceq.mm"
include "iccid.mm"
include "3ad2ant1.mm"
include "uneq2d.mm"
include "cle.mm"
include "simp1.mm"
include "simp2.mm"
include "xrleid.mm"
include "simp3.mm"
include "df-icc.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrltnle.mm"
include "df-ico.mm"
include "xrlelttr.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simprr.mm"
include "xrltled.mm"
include "ex.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "3eqtr3a.mm"

theorem snunioo1
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> ( ( A (,) B ) u. { A } ) = ( A [,) B ) )

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
    clt
    wbr
    #
    w3a
    #
    cA
    cB
    cioo
    co
    #
    cA
    cA
    cicc
    co
    #
    cun
    @5
    @4
    cun
    #
    @4
    cA
    csn
    #
    cun
    cA
    cB
    cico
    co
    #
    @4
    @5
    uncom
    @3
    @5
    @7
    @4
    @0
    @1
    @5
    @7
    wceq
    @2
    cA
    iccid
    3ad2ant1
    uneq2d
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
    cioo
    cico
    cle
    cle
    clt
    clt
    cicc
    cle
    clt
    vx
    vy
    vz
    df-icc
    vx
    vy
    vz
    df-ioo
    cA
    vw
    cv
    #
    xrltnle
    vx
    vy
    vz
    df-ico
    @11
    cA
    cB
    xrlelttr
    @0
    @0
    @11
    cxr
    wcel
    #
    w3a
    #
    @9
    cA
    @11
    clt
    wbr
    #
    wa
    #
    cA
    @11
    cle
    wbr
    @13
    @15
    wa
    cA
    @11
    @0
    @0
    @12
    @15
    simpl1
    @0
    @0
    @12
    @15
    simpl3
    @13
    @9
    @14
    simprr
    xrltled
    ex
    ixxun
    syl32anc
    3eqtr3a
end
