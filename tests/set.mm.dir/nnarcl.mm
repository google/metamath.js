include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "com.mm"
include "wss.mm"
include "wi.mm"
include "oaword1.mm"
include "word.mm"
include "eloni.mm"
include "ordom.mm"
include "ordtr2.mm"
include "sylancl.mm"
include "expd.mm"
include "adantr.mm"
include "mpd.mm"
include "oaword2.mm"
include "ancoms.mm"
include "adantl.mm"
include "jcad.mm"
include "nnacl.mm"
include "impbid1.mm"

theorem nnarcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( ( A +o B ) e. _om <-> ( A e. _om /\ B e. _om ) ) )

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
    coa
    co
    #
    com
    wcel
    #
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    @2
    @4
    @5
    @6
    @2
    cA
    @3
    wss
    #
    @4
    @5
    wi
    #
    cA
    cB
    oaword1
    @0
    @7
    @8
    wi
    @1
    @0
    @7
    @4
    @5
    @0
    cA
    word
    com
    word
    #
    @7
    @4
    wa
    @5
    wi
    cA
    eloni
    ordom
    cA
    @3
    com
    ordtr2
    sylancl
    expd
    adantr
    mpd
    @2
    cB
    @3
    wss
    #
    @4
    @6
    wi
    #
    @1
    @0
    @10
    cB
    cA
    oaword2
    ancoms
    @1
    @10
    @11
    wi
    @0
    @1
    @10
    @4
    @6
    @1
    cB
    word
    @9
    @10
    @4
    wa
    @6
    wi
    cB
    eloni
    ordom
    cB
    @3
    com
    ordtr2
    sylancl
    expd
    adantl
    mpd
    jcad
    cA
    cB
    nnacl
    impbid1
end
