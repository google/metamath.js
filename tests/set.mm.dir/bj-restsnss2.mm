include "wss.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "df-ss.mm"
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

theorem bj-restsnss2
  let cA: class A
  let cV: class V
  let cY: class Y


  assert |- ( ( A e. V /\ Y C_ A ) -> ( { Y } |`t A ) = { Y } )

  proof
    cY
    cA
    wss
    #
    cY
    cA
    cin
    #
    csn
    #
    cY
    csn
    #
    wceq
    #
    cA
    cV
    wcel
    #
    @3
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
    cY
    wceq
    @4
    cY
    cA
    df-ss
    @1
    cY
    sneq
    sylbi
    @5
    @0
    cY
    cvv
    wcel
    #
    @7
    @0
    @5
    @9
    cY
    cA
    cV
    ssexg
    ancoms
    @9
    @5
    @7
    cA
    cvv
    cV
    cY
    bj-restsn
    ancoms
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
