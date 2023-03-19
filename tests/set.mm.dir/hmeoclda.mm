include "ctop.mm"
include "wcel.mm"
include "chmeo.mm"
include "co.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccn.mm"
include "ccld.mm"
include "cfv.mm"
include "cima.mm"
include "hmeocnvcn.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "imacnvcnv.mm"
include "cnclima.mm"
include "syl5eqelr.mm"
include "sylan.mm"

theorem hmeoclda
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( ( J e. Top /\ K e. Top /\ F e. ( J Homeo K ) ) /\ S e. ( Clsd ` J ) ) -> ( F " S ) e. ( Clsd ` K ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    w3a
    cF
    ccnv
    #
    cK
    cJ
    ccn
    co
    wcel
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cF
    cS
    cima
    #
    cK
    ccld
    cfv
    #
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    hmeocnvcn
    3ad2ant3
    @4
    @5
    wa
    @6
    @3
    ccnv
    cS
    cima
    @7
    cF
    cS
    imacnvcnv
    cS
    @3
    cK
    cJ
    cnclima
    syl5eqelr
    sylan
end
