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
include "cioc.mm"
include "wceq.mm"
include "simp2.mm"
include "iccid.mm"
include "syl.mm"
include "uneq2d.mm"
include "cle.mm"
include "simp1.mm"
include "simp3.mm"
include "xrleid.mm"
include "df-ioo.mm"
include "df-icc.mm"
include "cv.mm"
include "xrlenlt.mm"
include "df-ioc.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "xrltled.mm"
include "ex.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "eqtr3d.mm"

theorem snunioo2
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> ( ( A (,) B ) u. { B } ) = ( A (,] B ) )

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
    cB
    cB
    cicc
    co
    #
    cun
    #
    @4
    cB
    csn
    #
    cun
    cA
    cB
    cioc
    co
    #
    @3
    @5
    @7
    @4
    @3
    @1
    @5
    @7
    wceq
    @0
    @1
    @2
    simp2
    #
    cB
    iccid
    syl
    uneq2d
    @3
    @0
    @1
    @1
    @2
    cB
    cB
    cle
    wbr
    #
    @6
    @8
    wceq
    @0
    @1
    @2
    simp1
    @9
    @9
    @0
    @1
    @2
    simp3
    @3
    @1
    @10
    @9
    cB
    xrleid
    syl
    vx
    vy
    vz
    vw
    cA
    cB
    cB
    cicc
    cioc
    clt
    clt
    cle
    cle
    cioo
    clt
    cle
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-icc
    cB
    vw
    cv
    #
    xrlenlt
    vx
    vy
    vz
    df-ioc
    @11
    cxr
    wcel
    #
    @1
    @1
    w3a
    #
    @11
    cB
    clt
    wbr
    #
    @10
    wa
    #
    @11
    cB
    cle
    wbr
    @13
    @15
    wa
    @11
    cB
    @12
    @1
    @1
    @15
    simpl1
    @12
    @1
    @1
    @15
    simpl2
    @13
    @14
    @10
    simprl
    xrltled
    ex
    cA
    cB
    @11
    xrltletr
    ixxun
    syl32anc
    eqtr3d
end
