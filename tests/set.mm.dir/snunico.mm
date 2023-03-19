include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cico.mm"
include "co.mm"
include "cicc.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "simp2.mm"
include "iccid.mm"
include "syl.mm"
include "uneq2d.mm"
include "simp1.mm"
include "simp3.mm"
include "xrleid.mm"
include "clt.mm"
include "df-ico.mm"
include "df-icc.mm"
include "cv.mm"
include "xrlenlt.mm"
include "wi.mm"
include "xrltle.mm"
include "3adant3.mm"
include "adantrd.mm"
include "xrletr.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "eqtr3d.mm"

theorem snunico
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> ( ( A [,) B ) u. { B } ) = ( A [,] B ) )

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
    cB
    cico
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
    cicc
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
    cicc
    cle
    clt
    cle
    cle
    cico
    cle
    cle
    vx
    vy
    vz
    df-ico
    vx
    vy
    vz
    df-icc
    #
    cB
    vw
    cv
    #
    xrlenlt
    @11
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
    xrletr
    ixxun
    syl32anc
    eqtr3d
end
