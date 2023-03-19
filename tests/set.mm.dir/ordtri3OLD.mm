include "word.mm"
include "wa.mm"
include "wceq.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "ordirr.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ib.mm"
include "syl5ibr.mm"
include "anim12d.mm"
include "com12.mm"
include "pm4.56.mm"
include "syl6ib.mm"
include "w3o.mm"
include "ordtri3or.mm"
include "df-3or.mm"
include "sylib.mm"
include "or32.mm"
include "ord.mm"
include "impbid.mm"

theorem ordtri3OLD
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A = B <-> -. ( A e. B \/ B e. A ) ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    cA
    cB
    wceq
    #
    cA
    cB
    wcel
    #
    cB
    cA
    wcel
    #
    wo
    #
    wn
    #
    @2
    @3
    @4
    wn
    #
    @5
    wn
    #
    wa
    #
    @7
    @3
    @2
    @10
    @3
    @0
    @8
    @1
    @9
    @0
    cA
    cA
    wcel
    #
    wn
    @3
    @8
    cA
    ordirr
    @3
    @11
    @4
    cA
    cB
    cA
    eleq2
    notbid
    syl5ib
    @1
    @9
    @3
    cB
    cB
    wcel
    #
    wn
    cB
    ordirr
    @3
    @5
    @12
    cA
    cB
    cB
    eleq2
    notbid
    syl5ibr
    anim12d
    com12
    @4
    @5
    pm4.56
    syl6ib
    @2
    @6
    @3
    @2
    @4
    @3
    wo
    @5
    wo
    #
    @6
    @3
    wo
    @2
    @4
    @3
    @5
    w3o
    @13
    cA
    cB
    ordtri3or
    @4
    @3
    @5
    df-3or
    sylib
    @4
    @3
    @5
    or32
    sylib
    ord
    impbid
end
