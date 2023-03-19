include "word.mm"
include "c0.mm"
include "wcel.mm"
include "wne.mm"
include "ne0i.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "ord0.mm"
include "wa.mm"
include "wn.mm"
include "noel.mm"
include "ordtri2.mm"
include "con2bid.mm"
include "mpbiri.mm"
include "mpan2.mm"
include "neor.mm"
include "sylib.mm"
include "impbid2.mm"

theorem ord0eln0
  let cA: class A


  assert |- ( Ord A -> ( (/) e. A <-> A =/= (/) ) )

  proof
    cA
    word
    #
    c0
    cA
    wcel
    #
    cA
    c0
    wne
    #
    cA
    c0
    ne0i
    @0
    cA
    c0
    wceq
    @1
    wo
    #
    @2
    @1
    wi
    @0
    c0
    word
    #
    @3
    ord0
    @0
    @4
    wa
    #
    @3
    cA
    c0
    wcel
    #
    wn
    cA
    noel
    @5
    @6
    @3
    cA
    c0
    ordtri2
    con2bid
    mpbiri
    mpan2
    @1
    cA
    c0
    neor
    sylib
    impbid2
end
