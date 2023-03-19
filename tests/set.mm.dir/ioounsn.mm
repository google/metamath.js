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
include "iccid.mm"
include "3ad2ant2.mm"
include "uneq2d.mm"
include "cle.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "3adant3.mm"
include "simp3.mm"
include "xrleid.mm"
include "df-ioo.mm"
include "df-icc.mm"
include "cv.mm"
include "xrlenlt.mm"
include "df-ioc.mm"
include "wi.mm"
include "xrltle.mm"
include "adantrd.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "syl12anc.mm"
include "eqtr3d.mm"

theorem ioounsn
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
    @1
    @0
    @5
    @7
    wceq
    @2
    cB
    iccid
    3ad2ant2
    uneq2d
    @3
    @0
    @1
    @1
    w3a
    #
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
    @9
    @2
    @0
    @1
    wa
    @0
    @1
    @1
    @0
    @1
    simpl
    @0
    @1
    simpr
    #
    @11
    3jca
    3adant3
    @0
    @1
    @2
    simp3
    @1
    @0
    @10
    @2
    cB
    xrleid
    3ad2ant2
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
    @12
    cxr
    wcel
    #
    @1
    @1
    w3a
    @12
    cB
    clt
    wbr
    #
    @12
    cB
    cle
    wbr
    #
    @10
    @13
    @1
    @14
    @15
    wi
    @1
    @12
    cB
    xrltle
    3adant3
    adantrd
    cA
    cB
    @12
    xrltletr
    ixxun
    syl12anc
    eqtr3d
end
