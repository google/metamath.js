include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "carddomi2.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "brdom2.mm"
include "wn.mm"
include "cardon.mm"
include "onelssi.mm"
include "wi.mm"
include "ancoms.mm"
include "domnsym.mm"
include "syl56.mm"
include "con2d.mm"
include "con0.mm"
include "wb.mm"
include "ontri1.mm"
include "mp2an.mm"
include "syl6ibr.mm"
include "wceq.mm"
include "carden2b.mm"
include "eqimss.mm"
include "syl.mm"
include "a1i.mm"
include "jaod.mm"
include "syl5bi.mm"
include "impbid.mm"

theorem carddom2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( ( card ` A ) C_ ( card ` B ) <-> A ~<_ B ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wss
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    @0
    carddomi2
    @7
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wo
    @3
    @6
    cA
    cB
    brdom2
    @3
    @8
    @6
    @9
    @3
    @8
    @5
    @4
    wcel
    #
    wn
    #
    @6
    @3
    @10
    @8
    @10
    @5
    @4
    wss
    #
    @3
    cB
    cA
    cdom
    wbr
    #
    @8
    wn
    @4
    @5
    cA
    cardon
    #
    onelssi
    @2
    @1
    @12
    @13
    wi
    cB
    cA
    @0
    carddomi2
    ancoms
    cB
    cA
    domnsym
    syl56
    con2d
    @4
    con0
    wcel
    @5
    con0
    wcel
    @6
    @11
    wb
    @14
    cB
    cardon
    @4
    @5
    ontri1
    mp2an
    syl6ibr
    @9
    @6
    wi
    @3
    @9
    @4
    @5
    wceq
    @6
    cA
    cB
    carden2b
    @4
    @5
    eqimss
    syl
    a1i
    jaod
    syl5bi
    impbid
end
