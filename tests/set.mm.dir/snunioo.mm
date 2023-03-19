include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "cun.mm"
include "csn.mm"
include "cico.mm"
include "wceq.mm"
include "simp1.mm"
include "iccid.mm"
include "syl.mm"
include "uneq1d.mm"
include "cle.mm"
include "simp2.mm"
include "xrleid.mm"
include "simp3.mm"
include "df-icc.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrltnle.mm"
include "df-ico.mm"
include "xrlelttr.mm"
include "wi.mm"
include "xrltle.mm"
include "3adant1.mm"
include "adantld.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "eqtr3d.mm"

theorem snunioo
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> ( { A } u. ( A (,) B ) ) = ( A [,) B ) )

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
    cA
    cicc
    co
    #
    cA
    cB
    cioo
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
    cico
    co
    #
    @3
    @4
    @7
    @5
    @3
    @0
    @4
    @7
    wceq
    @0
    @1
    @2
    simp1
    #
    cA
    iccid
    syl
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
    @9
    @9
    @0
    @1
    @2
    simp2
    @3
    @0
    @10
    @9
    cA
    xrleid
    syl
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
    cA
    @11
    clt
    wbr
    #
    cA
    @11
    cle
    wbr
    #
    @10
    @0
    @12
    @13
    @14
    wi
    @0
    cA
    @11
    xrltle
    3adant1
    adantld
    ixxun
    syl32anc
    eqtr3d
end
