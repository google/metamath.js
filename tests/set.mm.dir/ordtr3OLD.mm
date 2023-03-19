include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "simpr.mm"
include "ordelord.mm"
include "adantlr.mm"
include "ordtri1.mm"
include "syl2an2r.mm"
include "wi.mm"
include "ordtr2.mm"
include "ancoms.mm"
include "expcomd.mm"
include "imp.mm"
include "sylbird.mm"
include "orrd.mm"
include "ex.mm"

theorem ordtr3OLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord B /\ Ord C ) -> ( A e. B -> ( A e. C \/ C e. B ) ) )

  proof
    cB
    word
    #
    cC
    word
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    cC
    cB
    wcel
    #
    wo
    @2
    @3
    wa
    #
    @4
    @5
    @6
    @4
    wn
    #
    cC
    cA
    wss
    #
    @5
    @2
    @1
    @3
    cA
    word
    #
    @8
    @7
    wb
    @0
    @1
    simpr
    @0
    @3
    @9
    @1
    cB
    cA
    ordelord
    adantlr
    cC
    cA
    ordtri1
    syl2an2r
    @2
    @3
    @8
    @5
    wi
    @2
    @8
    @3
    @5
    @1
    @0
    @8
    @3
    wa
    @5
    wi
    cC
    cA
    cB
    ordtr2
    ancoms
    expcomd
    imp
    sylbird
    orrd
    ex
end
