include "cumgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cs3.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "eqid.mm"
include "umgrwwlks2on.mm"
include "wb.mm"
include "3anrev.mm"
include "sylan2b.mm"
include "prcom.mm"
include "eleq1i.mm"
include "anbi12ci.mm"
include "syl6rbb.mm"
include "bitrd.mm"

theorem wwlks2onsym
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cV: class V
  assume elwwlks2on.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. UMGraph /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( <" A B C "> e. ( A ( 2 WWalksNOn G ) C ) <-> <" C B A "> e. ( C ( 2 WWalksNOn G ) A ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cs3
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    #
    co
    wcel
    cA
    cB
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    cB
    cC
    cpr
    #
    @8
    wcel
    #
    wa
    #
    cC
    cB
    cA
    cs3
    cC
    cA
    @6
    co
    wcel
    #
    cA
    cB
    cC
    @8
    cG
    cV
    elwwlks2on.v
    @8
    eqid
    #
    umgrwwlks2on
    @5
    @13
    cC
    cB
    cpr
    #
    @8
    wcel
    #
    cB
    cA
    cpr
    #
    @8
    wcel
    #
    wa
    #
    @12
    @4
    @0
    @3
    @2
    @1
    w3a
    @13
    @19
    wb
    @1
    @2
    @3
    3anrev
    cC
    cB
    cA
    @8
    cG
    cV
    elwwlks2on.v
    @14
    umgrwwlks2on
    sylan2b
    @16
    @11
    @18
    @9
    @15
    @10
    @8
    cC
    cB
    prcom
    eleq1i
    @17
    @7
    @8
    cB
    cA
    prcom
    eleq1i
    anbi12ci
    syl6rbb
    bitrd
end
