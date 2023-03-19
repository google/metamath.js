include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wa.mm"
include "wi.mm"
include "wn.mm"
include "xrltletr.mm"
include "wo.mm"
include "id.mm"
include "impcom.mm"
include "wb.mm"
include "xrltnle.mm"
include "3adant2.mm"
include "biimpd.mm"
include "imp.mm"
include "olcd.mm"
include "expcom.mm"
include "syl.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"
include "orcd.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "df-3an.mm"
include "notbii.mm"
include "ianor.mm"
include "bitri.mm"
include "sylibr.mm"
include "mpd.mm"

theorem nltle2tri
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> -. ( A < B /\ B <_ C /\ C <_ A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    wa
    #
    cA
    cC
    clt
    wbr
    #
    wi
    #
    @4
    @5
    cC
    cA
    cle
    wbr
    #
    w3a
    #
    wn
    #
    cA
    cB
    cC
    xrltletr
    @3
    @8
    @11
    @3
    @8
    wa
    #
    @6
    wn
    #
    @9
    wn
    #
    wo
    #
    @11
    @6
    @12
    @15
    wi
    @6
    @3
    @8
    @15
    @6
    @8
    @3
    @15
    @6
    @8
    @3
    @15
    wi
    #
    @6
    @8
    wa
    @7
    @16
    @8
    @6
    @7
    @8
    id
    impcom
    @3
    @7
    @15
    @3
    @7
    wa
    @14
    @13
    @3
    @7
    @14
    @3
    @7
    @14
    @0
    @2
    @7
    @14
    wb
    @1
    cA
    cC
    xrltnle
    3adant2
    biimpd
    imp
    olcd
    expcom
    syl
    ex
    com23
    impd
    @13
    @15
    @12
    @13
    @13
    @14
    @13
    id
    orcd
    a1d
    pm2.61i
    @11
    @6
    @9
    wa
    #
    wn
    @15
    @10
    @17
    @4
    @5
    @9
    df-3an
    notbii
    @6
    @9
    ianor
    bitri
    sylibr
    ex
    mpd
end
