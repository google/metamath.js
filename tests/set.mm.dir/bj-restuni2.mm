include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "uniexg.mm"
include "ssexg.mm"
include "sylan2.mm"
include "ancoms.mm"
include "bj-restuni.mm"
include "syldan.mm"
include "inss2.mm"
include "a1i.mm"
include "id.mm"
include "ssid.mm"
include "ssind.mm"
include "eqssd.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem bj-restuni2
  let cA: class A
  let cV: class V
  let cX: class X


  assert |- ( ( X e. V /\ A C_ U. X ) -> U. ( X |`t A ) = A )

  proof
    cX
    cV
    wcel
    #
    cA
    cX
    cuni
    #
    wss
    #
    wa
    cX
    cA
    crest
    co
    cuni
    #
    @1
    cA
    cin
    #
    cA
    @0
    @2
    cA
    cvv
    wcel
    #
    @3
    @4
    wceq
    @2
    @0
    @5
    @0
    @2
    @1
    cvv
    wcel
    @5
    cX
    cV
    uniexg
    cA
    @1
    cvv
    ssexg
    sylan2
    ancoms
    cA
    cV
    cvv
    cX
    bj-restuni
    syldan
    @2
    @4
    cA
    wceq
    @0
    @2
    @4
    cA
    @4
    cA
    wss
    @2
    @1
    cA
    inss2
    a1i
    @2
    cA
    @1
    cA
    @2
    id
    cA
    cA
    wss
    @2
    cA
    ssid
    a1i
    ssind
    eqssd
    adantl
    eqtrd
end
