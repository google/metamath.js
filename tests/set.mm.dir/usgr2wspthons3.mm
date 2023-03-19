include "cusgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cs3.mm"
include "c2.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "wne.mm"
include "cwwlksnon.mm"
include "cpr.mm"
include "wb.mm"
include "wi.mm"
include "cn.mm"
include "c0.mm"
include "2nn.mm"
include "ne0i.mm"
include "wspthsnonn0vne.mm"
include "sylancr.mm"
include "simplr.mm"
include "wpthswwlks2on.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "jca.mm"
include "exp31.mm"
include "com13.mm"
include "mpd.mm"
include "com12.mm"
include "biimprd.mm"
include "expimpd.mm"
include "impbid.mm"
include "adantr.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "umgrwwlks2on.mm"
include "sylan.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem usgr2wspthons3
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  assume usgr2wspthon0.v: |- V = ( Vtx ` G )
  assume usgr2wspthon0.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( <" A B C "> e. ( A ( 2 WSPathsNOn G ) C ) <-> ( A =/= C /\ { A , B } e. E /\ { B , C } e. E ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cs3
    #
    cA
    cC
    c2
    cG
    cwwspthsnon
    co
    co
    #
    wcel
    #
    cA
    cC
    wne
    #
    @3
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    #
    wcel
    #
    wa
    #
    @6
    cA
    cB
    cpr
    cE
    wcel
    #
    cB
    cC
    cpr
    cE
    wcel
    #
    w3a
    #
    @0
    @5
    @9
    wb
    @1
    @0
    @5
    @9
    @5
    @0
    @9
    @5
    @6
    @0
    @9
    wi
    @5
    c2
    cn
    wcel
    @4
    c0
    wne
    @6
    2nn
    @4
    @3
    ne0i
    cG
    c2
    cA
    cC
    wspthsnonn0vne
    sylancr
    @0
    @6
    @5
    @9
    @0
    @6
    @5
    @9
    @0
    @6
    wa
    #
    @5
    wa
    @6
    @8
    @0
    @6
    @5
    simplr
    @13
    @5
    @8
    @13
    @4
    @7
    @3
    cA
    cC
    cG
    wpthswwlks2on
    eleq2d
    #
    biimpa
    jca
    exp31
    com13
    mpd
    com12
    @0
    @6
    @8
    @5
    @13
    @5
    @8
    @14
    biimprd
    expimpd
    impbid
    adantr
    @2
    @9
    @6
    @10
    @11
    wa
    #
    wa
    @12
    @2
    @8
    @15
    @6
    @0
    cG
    cumgr
    wcel
    @1
    @8
    @15
    wb
    cG
    usgrumgr
    cA
    cB
    cC
    cE
    cG
    cV
    usgr2wspthon0.v
    usgr2wspthon0.e
    umgrwwlks2on
    sylan
    anbi2d
    @6
    @10
    @11
    3anass
    syl6bbr
    bitrd
end
