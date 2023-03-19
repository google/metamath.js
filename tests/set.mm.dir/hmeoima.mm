include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "ccn.mm"
include "cima.mm"
include "hmeocnvcn.mm"
include "wa.mm"
include "imacnvcnv.mm"
include "cnima.mm"
include "syl5eqelr.mm"
include "sylan.mm"

theorem hmeoima
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( F e. ( J Homeo K ) /\ A e. J ) -> ( F " A ) e. K )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    cF
    ccnv
    #
    cK
    cJ
    ccn
    co
    wcel
    #
    cA
    cJ
    wcel
    #
    cF
    cA
    cima
    #
    cK
    wcel
    cF
    cJ
    cK
    hmeocnvcn
    @1
    @2
    wa
    @3
    @0
    ccnv
    cA
    cima
    cK
    cF
    cA
    imacnvcnv
    cA
    @0
    cK
    cJ
    cnima
    syl5eqelr
    sylan
end
