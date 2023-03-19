include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cale.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "onsseleq.mm"
include "csdm.mm"
include "alephord.mm"
include "sdomdom.mm"
include "syl6bi.mm"
include "cen.mm"
include "wi.mm"
include "cvv.mm"
include "fvex.mm"
include "fveq2.mm"
include "eqeng.mm"
include "mpsyl.mm"
include "a1i.mm"
include "endom.mm"
include "syl6.mm"
include "jaod.mm"
include "sylbid.mm"
include "wn.mm"
include "word.mm"
include "eloni.mm"
include "ordtri2or.mm"
include "syl2anr.mm"
include "ord.mm"
include "con1d.mm"
include "wb.mm"
include "ancoms.mm"
include "sdomnen.mm"
include "sbth.mm"
include "ex.mm"
include "syl.mm"
include "mtod.mm"
include "syld.mm"
include "impcon4bid.mm"

theorem alephdom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> ( aleph ` A ) ~<_ ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    cale
    cfv
    #
    cB
    cale
    cfv
    #
    cdom
    wbr
    #
    @2
    @3
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    @6
    cA
    cB
    onsseleq
    @2
    @7
    @6
    @8
    @2
    @7
    @4
    @5
    csdm
    wbr
    @6
    cA
    cB
    alephord
    @4
    @5
    sdomdom
    syl6bi
    @2
    @8
    @4
    @5
    cen
    wbr
    #
    @6
    @8
    @9
    wi
    @2
    @4
    cvv
    wcel
    @8
    @4
    @5
    wceq
    @9
    cA
    cale
    fvex
    cA
    cB
    cale
    fveq2
    @4
    @5
    cvv
    eqeng
    mpsyl
    a1i
    @4
    @5
    endom
    syl6
    jaod
    sylbid
    @2
    @3
    wn
    cB
    cA
    wcel
    #
    @6
    wn
    #
    @2
    @10
    @3
    @2
    @10
    @3
    @1
    cB
    word
    cA
    word
    @10
    @3
    wo
    @0
    cB
    eloni
    cA
    eloni
    cB
    cA
    ordtri2or
    syl2anr
    ord
    con1d
    @2
    @10
    @5
    @4
    csdm
    wbr
    #
    @11
    @1
    @0
    @10
    @12
    wb
    cB
    cA
    alephord
    ancoms
    @12
    @6
    @5
    @4
    cen
    wbr
    #
    @5
    @4
    sdomnen
    @12
    @5
    @4
    cdom
    wbr
    #
    @6
    @13
    wi
    @5
    @4
    sdomdom
    @14
    @6
    @13
    @5
    @4
    sbth
    ex
    syl
    mtod
    syl6bi
    syld
    impcon4bid
end
