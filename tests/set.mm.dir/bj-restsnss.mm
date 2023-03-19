include "wss.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "sseqin2.mm"
include "sneq.mm"
include "sylbi.mm"
include "cvv.mm"
include "ssexg.mm"
include "ancoms.mm"
include "bj-restsn.mm"
include "syldan.mm"
include "eqeq2.mm"
include "biimpa.mm"
include "syl2an2.mm"

theorem bj-restsnss
  let cA: class A
  let cV: class V
  let cY: class Y


  assert |- ( ( Y e. V /\ A C_ Y ) -> ( { Y } |`t A ) = { A } )

  proof
    cA
    cY
    wss
    #
    cY
    cA
    cin
    #
    csn
    #
    cA
    csn
    #
    wceq
    #
    cY
    cV
    wcel
    #
    cY
    csn
    cA
    crest
    co
    #
    @2
    wceq
    #
    @6
    @3
    wceq
    #
    @0
    @1
    cA
    wceq
    @4
    cA
    cY
    sseqin2
    @1
    cA
    sneq
    sylbi
    @5
    @0
    cA
    cvv
    wcel
    #
    @7
    @0
    @5
    @9
    cA
    cY
    cV
    ssexg
    ancoms
    cA
    cV
    cvv
    cY
    bj-restsn
    syldan
    @4
    @7
    @8
    @2
    @3
    @6
    eqeq2
    biimpa
    syl2an2
end
