include "word.mm"
include "con0.mm"
include "wss.mm"
include "ordon.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "ordeleqon.mm"
include "biimpi.mm"
include "adantr.mm"
include "ordsseleq.mm"
include "mpbird.mm"
include "mpan2.mm"

theorem ordsson
  let cA: class A


  assert |- ( Ord A -> A C_ On )

  proof
    cA
    word
    #
    con0
    word
    #
    cA
    con0
    wss
    #
    ordon
    @0
    @1
    wa
    @2
    cA
    con0
    wcel
    cA
    con0
    wceq
    wo
    #
    @0
    @3
    @1
    @0
    @3
    cA
    ordeleqon
    biimpi
    adantr
    cA
    con0
    ordsseleq
    mpbird
    mpan2
end
